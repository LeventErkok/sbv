-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.Array
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Persistent functional-array lowering for the SBV-to-C compiler.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.Array
  ( arrayKinds
  , arrayCType
  , arrayInputCType
  , arrayOutputCType
  , arrayForwardTypeDecls
  , arrayOutputReadName
  , arrayOutputReleaseName
  , arrayExportName
  , arrayStoredValue
  , arrayStoredLoad
  , arrayTypeDecls
  , arrayRuntime
  , arrayContextStart
  , arrayContextEnd
  , arrayInputSetup
  , arrayDriverCallback
  , arrayDriverInput
  , arrayDriverStoredInput
  , arrayLambdaName
  , arrayConst
  , arrayExpr
  , arrayReadName
  , arrayEqualName
  ) where

import Data.List (nubBy, tails)

import qualified Data.Set as Set
import qualified Data.Text as T

import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as P ((<>), render)

import Data.SBV.Compilers.C.BV         (isWideBV)
import Data.SBV.Compilers.C.GMP        (gmpFunctionName, gmpNewName, gmpOutputType, isExactGMPKind)
import Data.SBV.Compilers.C.Lowering   (CLowering(..), CRequirement(..), expressionLowering)
import Data.SBV.Compilers.C.Syntax     (cUnusedAttribute, cCommentText)
import Data.SBV.Compilers.C.Types      ( isConcreteADT
                                       , constElementCType
                                       , arrayKindTag
                                       , arrayOutputCTypeName
                                       , arrayStoredCloneName
                                       , arrayStoredReleaseName
                                       , elementCType
                                       )
import Data.SBV.Compilers.C.Value      (byValueEqual, managedValueClone, managedValueRelease, valueNeedsOwnership)
import Data.SBV.Compilers.CodeGen      (CgConfig)
import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic          (smtLambdaInfo)

-- | Return and validate the distinct array kinds used by a program. Arrays may
-- occur as values, but not as keys: array-key matching would require general
-- extensional equality, which the C backend cannot implement for arbitrary
-- domains. Deduplicate by C type: Boolean and unsigned one-bit keys or values
-- have the same representation and share their runtime helpers.
arrayKinds :: Set.Set Kind -> [Kind]
arrayKinds = nubBy (\left right -> arrayCType left == arrayCType right) . map validate . filter isArray . Set.toAscList
 where validate k@(KArray keyKind valueKind)
         | isArray keyKind
         = error $ "SBV->C: Array-valued array keys require unsupported extensional equality: " ++ show k
         | supported keyKind && supported valueKind
         = k
         | True
         = error $ "SBV->C: Array kind is not yet supported: " ++ show k
       validate kind = error $ "SBV->C: Expected an array kind, received " ++ show kind

       supported kind = case kind of
         KBool                    -> True
         KBounded{}               -> True
         KUnbounded               -> True
         KReal                    -> True
         KRational                -> True
         KFloat                   -> True
         KDouble                  -> True
         KFP{}                    -> True
         KChar                    -> True
         KString                  -> True
         KList elementKind        -> supported elementKind
         KSet elementKind         -> supported elementKind
         KTuple fields            -> all supported fields
         KArray keyKind valueKind -> not (isArray keyKind) && supported keyKind && supported valueKind
         KADT{}                   -> isRoundingMode kind || isConcreteADT kind
         _                        -> False

-- | Return the public opaque-pointer type used for an SBV array kind.
arrayCType :: Kind -> String
arrayCType kind@KArray{} = "SBVArray_" ++ arrayKindTag kind
arrayCType kind          = error $ "SBV->C: Expected an array kind, received " ++ show kind

-- | Return the public callback-descriptor type accepted for an array-valued
-- C input. The descriptor and its context are borrowed for the duration of
-- the generated call.
arrayInputCType :: Kind -> String
arrayInputCType kind = "SBVArrayInput_" ++ arraySuffix kind

-- | Return the public owned-descriptor type produced for an array-valued C
-- output or return value.
arrayOutputCType :: Kind -> String
arrayOutputCType = arrayOutputCTypeName

-- | Return the public helper name used to read an owned array output.
arrayOutputReadName :: Kind -> String
arrayOutputReadName kind = "sbv_array_output_read_" ++ arraySuffix kind

-- | Return the public helper name used to release an owned array output.
arrayOutputReleaseName :: Kind -> String
arrayOutputReleaseName kind = "sbv_array_output_release_" ++ arraySuffix kind

-- | Return the public helper name used to retain an owned array output.
arrayOutputRetainName :: Kind -> String
arrayOutputRetainName kind = "sbv_array_output_retain_" ++ arraySuffix kind

-- | Return the public helper name used to borrow an owned output as an input
-- descriptor for another generated call.
arrayOutputAsInputName :: Kind -> String
arrayOutputAsInputName kind = "sbv_array_output_as_input_" ++ arraySuffix kind

-- | Return the internal helper name used to export a function-scoped array.
arrayExportName :: Kind -> String
arrayExportName kind = "sbv_array_export_" ++ arraySuffix kind

-- | Return the internal helper name that exports an array into the generated
-- function's temporary ownership arena.
arrayStoredExportName :: Kind -> String
arrayStoredExportName kind = "sbv_array_stored_export_" ++ arraySuffix kind

-- | Convert an internal array expression to the retained descriptor pointer
-- representation used when an array is stored inside another value. Other
-- kinds are returned unchanged.
arrayStoredValue :: Kind -> Doc -> Doc
arrayStoredValue kind value
  | isArray kind
  = text (arrayStoredExportName kind)
      P.<> parens (fsep (punctuate comma [text "&sbv_local_array_ctx", value]))
  | True
  = value

-- | Borrow a retained descriptor pointer as an internal array root for the
-- remainder of a generated call.
arrayStoredLoad :: SV -> Doc -> CLowering
arrayStoredLoad resultSV descriptor = CLowering
  { loweringExpression   = text "&" P.<> text nodeName
  , loweringDeclarations = [ text "const" <+> text (arrayOutputCType kind) <+> text "*" P.<> text descriptorName P.<> semi
                           , text (arrayNodeType kind) <+> text nodeName P.<> semi
                           ]
  , loweringSetup        = [ text descriptorName <+> text "=" <+> descriptor P.<> semi
                           , text "if" P.<> parens (text descriptorName <+> text "== NULL" <+> text "||" <+> text descriptorName P.<> text "->lookup == NULL")
                             <+> text "abort" P.<> parens empty P.<> semi
                           , text nodeName <+> text "=" <+> parens (text (arrayNodeType kind))
                             <+> braces (fsep (punctuate comma descriptorFields)) P.<> semi
                           ]
  , loweringRequirements = Set.singleton CRequiresArrays
  }
 where kind             = kindOf resultSV
       descriptorName   = "sbv_local_array_descriptor_" ++ show resultSV
       nodeName         = "sbv_local_array_" ++ show resultSV
       descriptorFields = [ text ".kind = SBV_ARRAY_CALLBACK"
                          , text ".lookup ="  <+> text descriptorName P.<> text "->lookup"
                          , text ".context =" <+> text descriptorName P.<> text "->context"
                          , text ".retain ="  <+> text descriptorName P.<> text "->retain"
                          , text ".release =" <+> text descriptorName P.<> text "->release"
                          ]

-- | Emit descriptor forward declarations needed by aggregate layouts that
-- store arrays by pointer. The complete descriptor remains delayed until its
-- key and value layouts are available.
arrayForwardTypeDecls :: [Kind] -> Doc
arrayForwardTypeDecls []    = empty
arrayForwardTypeDecls kinds = text . unlines $
     commonDeclarations
  ++ concatMap declaration kinds
 where commonDeclarations =
         [ "/* Forward declarations for retained array descriptors. */"
         , cUnusedAttribute
         , "#ifndef SBV_ARRAY_CONTEXT_LIFETIME_DEFINED"
         , "#define SBV_ARRAY_CONTEXT_LIFETIME_DEFINED"
         , "typedef const void *(*SBVArrayContextRetain)(const void *context);"
         , "typedef void (*SBVArrayContextRelease)(const void *context);"
         , "#endif"
         , ""
         ]

       declaration kind@KArray{} =
         [ "#ifndef " ++ arrayForwardGuard kind
         , "#define " ++ arrayForwardGuard kind
         , "typedef struct " ++ arrayOutputCType kind ++ " " ++ arrayOutputCType kind ++ ";"
         , "static inline SBV_CGEN_UNUSED " ++ arrayOutputCType kind ++ " *" ++ arrayStoredCloneName kind
        ++   "(const " ++ arrayOutputCType kind ++ " *value);"
         , "static inline SBV_CGEN_UNUSED void " ++ arrayStoredReleaseName kind
        ++   "(" ++ arrayOutputCType kind ++ " **value);"
         , "#endif"
         , ""
         ]
       declaration kind = error $ "SBV->C: Expected an array kind, received " ++ show kind

-- | Emit opaque public array types for every kind used by a generated
-- program. Input descriptors are borrowed during a call. Output descriptors
-- own retained contexts and must be released with their generated helper.
arrayTypeDecls :: [Kind] -> Doc
arrayTypeDecls [] = empty
arrayTypeDecls kinds = text . unlines $
     [ "/* Persistent functional arrays. Internal references are valid for one call. */"
     , "/* Input contexts are borrowed unless an escaping result invokes their retain */"
     , "/* callback. Owned outputs must be released with the generated release helper. */"
     , "/* Callback results borrow their context; aggregate reads borrow the array owner. */"
     , "/* Clone a managed read result to outlive its owner. The as_input helper only borrows. */"
     , "/* Lookups must be stable; escaping non-null contexts require both retain and release. */"
     ]
  ++ concatMap declaration kinds
 where declaration kind@(KArray keyKind valueKind)
         = let inputType       = arrayInputCType kind
               outputType      = arrayOutputCType kind
               lookupType      = arrayLookupType kind
               readOutput      = arrayOutputReadName kind
               retainOutput    = arrayOutputRetainName kind
               releaseOutput   = arrayOutputReleaseName kind
               asInput         = arrayOutputAsInputName kind
               cloneStored     = arrayStoredCloneName kind
               releaseStored   = arrayStoredReleaseName kind
               keyType         = elementCType keyKind
               valueType       = elementCType valueKind
           in [ "#ifndef " ++ arrayGuard kind
           , "#define " ++ arrayGuard kind
           , "/* Owned descriptors carry one reference. Retain copied descriptors and release each owner. */"
           , "/* The input adapter is borrowed; a generated callee retains it if the array escapes. */"
           , "#ifndef " ++ arrayForwardGuard kind
           , "#define " ++ arrayForwardGuard kind
           , "typedef struct " ++ outputType ++ " " ++ outputType ++ ";"
           , "static inline SBV_CGEN_UNUSED " ++ outputType ++ " *" ++ cloneStored ++ "(const " ++ outputType ++ " *value);"
           , "static inline SBV_CGEN_UNUSED void " ++ releaseStored ++ "(" ++ outputType ++ " **value);"
           , "#endif"
           , "typedef struct " ++ arrayNodeType kind ++ " " ++ arrayNodeType kind ++ ";"
           , "typedef const " ++ arrayNodeType kind ++ " *" ++ arrayCType kind ++ ";"
           , "typedef " ++ valueType ++ " (*" ++ lookupType ++ ")(const void *context, " ++ keyType ++ " key);"
           , "typedef struct { " ++ lookupType ++ " lookup; const void *context; SBVArrayContextRetain retain; SBVArrayContextRelease release; } " ++ inputType ++ ";"
           , "struct " ++ outputType ++ " { " ++ lookupType ++ " lookup; const void *context; SBVArrayContextRetain retain; SBVArrayContextRelease release; };"
           , "static inline " ++ valueType ++ " " ++ readOutput ++ "(" ++ outputType ++ " array, " ++ keyType ++ " key)"
           , "{ if (array.lookup == NULL) abort(); return array.lookup(array.context, key); }"
           , "static inline " ++ outputType ++ " " ++ retainOutput ++ "(" ++ outputType ++ " array)"
           , "{"
           , "  if (array.context != NULL) {"
           , "    if (array.retain == NULL) abort();"
           , "    array.context = array.retain(array.context);"
           , "    if (array.context == NULL) abort();"
           , "  }"
           , "  return array;"
           , "}"
           , "static inline void " ++ releaseOutput ++ "(" ++ outputType ++ " *array)"
           , "{ if (array == NULL) return; if (array->context != NULL) { if (array->release == NULL) abort(); array->release(array->context); } array->lookup = NULL; array->context = NULL; array->retain = NULL; array->release = NULL; }"
           , "static inline " ++ inputType ++ " " ++ asInput ++ "(" ++ outputType ++ " array)"
           , "{ " ++ inputType ++ " input = {array.lookup, array.context, array.retain, array.release}; return input; }"
           , "static inline SBV_CGEN_UNUSED " ++ outputType ++ " *" ++ cloneStored ++ "(const " ++ outputType ++ " *value)"
           , "{"
           , "  if (value == NULL) abort();"
           , "  " ++ outputType ++ " *copy = (" ++ outputType ++ " *) malloc(sizeof *copy);"
           , "  if (copy == NULL) abort();"
           , "  *copy = " ++ retainOutput ++ "(*value);"
           , "  return copy;"
           , "}"
           , "static inline SBV_CGEN_UNUSED void " ++ releaseStored ++ "(" ++ outputType ++ " **value)"
           , "{"
           , "  if (value == NULL || *value == NULL) return;"
           , "  " ++ releaseOutput ++ "(*value);"
           , "  free(*value);"
           , "  *value = NULL;"
           , "}"
           , "#endif"
           , ""
           ]
       declaration kind = error $ "SBV->C: Expected an array kind, received " ++ show kind

-- | Emit the node layouts and newest-write-first lookup helpers for every
-- array kind used by a generated program.
arrayRuntime :: CgConfig -> [Kind] -> Doc
arrayRuntime _   []    = empty
arrayRuntime cfg kinds = text . unlines $
     [ "/* Persistent functional-array runtime. */"
     , "typedef enum { SBV_ARRAY_CONSTANT, SBV_ARRAY_STORE, SBV_ARRAY_CALLBACK } SBVArrayNodeKind;"
     , "typedef struct sbv_array_temp sbv_array_temp;"
     , "struct sbv_array_temp { sbv_array_temp *next; void *value; void (*release)(void *value); };"
     , "typedef struct { sbv_array_temp *temporaries; } sbv_array_ctx;"
     , ""
     , "static SBV_CGEN_UNUSED void sbv_array_ctx_remember(sbv_array_ctx *ctx, void *value, void (*release)(void *value))"
     , "{"
     , "  if (ctx == NULL || value == NULL || release == NULL) abort();"
     , "  sbv_array_temp *temporary = (sbv_array_temp *) malloc(sizeof *temporary);"
     , "  if (temporary == NULL) abort();"
     , "  temporary->next = ctx->temporaries;"
     , "  temporary->value = value;"
     , "  temporary->release = release;"
     , "  ctx->temporaries = temporary;"
     , "}"
     , ""
     , "static SBV_CGEN_UNUSED void sbv_array_ctx_end(sbv_array_ctx *ctx)"
     , "{"
     , "  while (ctx != NULL && ctx->temporaries != NULL) {"
     , "    sbv_array_temp *temporary = ctx->temporaries;"
     , "    ctx->temporaries = temporary->next;"
     , "    temporary->release(temporary->value);"
     , "    free(temporary);"
     , "  }"
     , "}"
     , ""
     ]
  ++ concatMap runtime kinds
 where runtime kind@(KArray keyKind valueKind) =
         let nodeType    = arrayNodeType kind
             arrayType   = arrayCType kind
             keyType     = elementCType keyKind
             valueType   = elementCType valueKind
             readName    = arrayReadName kind
             keyEquality = P.render $ keyEqual cfg keyKind (text "array->key") (text "key")
         in [ "struct " ++ nodeType ++ " {"
            , "  SBVArrayNodeKind kind;"
            , "  " ++ arrayType ++ " parent;"
            , "  " ++ keyType ++ " key;"
            , "  " ++ valueType ++ " value;"
            , "  " ++ arrayLookupType kind ++ " lookup;"
            , "  const void *context;"
            , "  SBVArrayContextRetain retain;"
            , "  SBVArrayContextRelease release;"
            , "};"
            , ""
            , "static SBV_CGEN_UNUSED " ++ valueType ++ " " ++ readName ++ "(" ++ arrayType ++ " array, " ++ keyType ++ " key)"
            , "{"
            , "  while (array->kind == SBV_ARRAY_STORE) {"
            , "    if (" ++ keyEquality ++ ") return array->value;"
            , "    array = array->parent;"
            , "  }"
            , "  if (array->kind == SBV_ARRAY_CALLBACK) return array->lookup(array->context, key);"
            , "  return array->value;"
            , "}"
            , ""
            ]
         ++ ownershipRuntime cfg kind
         ++ storedArrayRuntime kind
       runtime kind = error $ "SBV->C: Expected an array kind, received " ++ show kind

-- | Emit the per-kind bridge that turns a call-scoped array node into an
-- owned descriptor pointer tracked by the function's temporary arena.
storedArrayRuntime :: Kind -> [String]
storedArrayRuntime kind@KArray{} =
  [ "static SBV_CGEN_UNUSED void " ++ releaseVoid ++ "(void *value)"
  , "{"
  , "  " ++ outputType ++ " *array = (" ++ outputType ++ " *) value;"
  , "  " ++ arrayOutputReleaseName kind ++ "(array);"
  , "  free(array);"
  , "}"
  , ""
  , "static SBV_CGEN_UNUSED " ++ outputType ++ " *" ++ exportStored
 ++   "(sbv_array_ctx *ctx, " ++ arrayCType kind ++ " array)"
  , "{"
  , "  " ++ outputType ++ " *result = (" ++ outputType ++ " *) malloc(sizeof *result);"
  , "  if (result == NULL) abort();"
  , "  *result = " ++ arrayExportName kind ++ "(array);"
  , "  sbv_array_ctx_remember(ctx, result, " ++ releaseVoid ++ ");"
  , "  return result;"
  , "}"
  , ""
  ]
 where outputType   = arrayOutputCType kind
       exportStored = arrayStoredExportName kind
       releaseVoid  = "sbv_array_stored_release_void_" ++ arraySuffix kind
storedArrayRuntime kind = error $ "SBV->C: Expected an array kind, received " ++ show kind

-- | Emit the heap owner used when an array escapes its generated call. Store
-- chains are copied, exact keys and values are duplicated into a private GMP
-- arena, managed aggregates are deep-copied, and callback contexts are
-- retained through their lifetime protocol.
ownershipRuntime :: CgConfig -> Kind -> [String]
ownershipRuntime cfg kind@(KArray keyKind valueKind) =
  [ "typedef struct {"
  , "  size_t references;"
  , "  size_t node_count;"
  , "  " ++ nodeType ++ " *nodes;"
  ]
  ++ ["  sbv_gmp_ctx exact_values;" | hasExact]
  ++ [ "  const void *base_context;"
     , "  SBVArrayContextRelease base_release;"
     , "} " ++ ownerType ++ ";"
     , ""
     , "static SBV_CGEN_UNUSED " ++ valueType ++ " " ++ ownedLookup ++ "(const void *context, " ++ keyType ++ " key)"
     , "{"
     , "  const " ++ ownerType ++ " *owner = (const " ++ ownerType ++ " *) context;"
     , "  return " ++ arrayReadName kind ++ "(&owner->nodes[0], key);"
     , "}"
     , ""
     , "static SBV_CGEN_UNUSED const void *" ++ ownedRetain ++ "(const void *context)"
     , "{"
     , "  " ++ ownerType ++ " *owner = (" ++ ownerType ++ " *) context;"
     , "  ++owner->references;"
     , "  return context;"
     , "}"
     , ""
     , "static SBV_CGEN_UNUSED void " ++ ownedRelease ++ "(const void *context)"
     , "{"
     , "  " ++ ownerType ++ " *owner = (" ++ ownerType ++ " *) context;"
     , "  if (--owner->references != 0) return;"
     , "  if (owner->base_release != NULL) owner->base_release(owner->base_context);"
     ]
  ++ releaseManagedFields
  ++ ["  sbv_gmp_ctx_end(&owner->exact_values);" | hasExact]
  ++ [ "  free(owner->nodes);"
     , "  free(owner);"
     , "}"
     , ""
     , "static SBV_CGEN_UNUSED " ++ outputType ++ " " ++ arrayExportName kind ++ "(" ++ arrayType ++ " array)"
     , "{"
     , "  size_t count = 1;"
     , "  " ++ arrayType ++ " cursor = array;"
     , "  if (cursor == NULL) abort();"
     , "  while (cursor->kind == SBV_ARRAY_STORE) { if (cursor->parent == NULL) abort(); ++count; cursor = cursor->parent; }"
     , "  " ++ ownerType ++ " *owner = (" ++ ownerType ++ " *) calloc(1, sizeof(*owner));"
     , "  if (owner == NULL) abort();"
     , "  owner->nodes = (" ++ nodeType ++ " *) calloc(count, sizeof(*owner->nodes));"
     , "  if (owner->nodes == NULL) { free(owner); abort(); }"
     , "  owner->references = 1;"
     , "  owner->node_count = count;"
     , "  " ++ arrayType ++ " source = array;"
     , "  for (size_t i = 0; i < count; ++i) {"
     , "    owner->nodes[i] = *source;"
     , "    if (source->kind == SBV_ARRAY_STORE) {"
     , "      owner->nodes[i].parent = &owner->nodes[i + 1];"
     ]
  ++ cloneExact "key" keyKind
  ++ cloneManaged "key" keyKind
  ++ [ "    }"
     , "    if (source->kind != SBV_ARRAY_CALLBACK) {"
     ]
  ++ cloneExact "value" valueKind
  ++ cloneManaged "value" valueKind
  ++ [ "    }"
     , "    if (source->kind == SBV_ARRAY_CALLBACK && source->context != NULL) {"
     , "      if (source->retain == NULL || source->release == NULL) abort();"
     , "      owner->base_context = source->retain(source->context);"
     , "      if (owner->base_context == NULL) abort();"
     , "      owner->base_release = source->release;"
     , "      owner->nodes[i].context = owner->base_context;"
     , "    }"
     , "    if (source->kind == SBV_ARRAY_STORE) source = source->parent;"
     , "  }"
     , "  " ++ outputType ++ " output = {" ++ ownedLookup ++ ", owner, " ++ ownedRetain ++ ", " ++ ownedRelease ++ "};"
     , "  return output;"
     , "}"
     , ""
     ]
 where nodeType      = arrayNodeType kind
       arrayType     = arrayCType kind
       inputSuffix   = arraySuffix kind
       ownerType     = "sbv_array_owner_" ++ inputSuffix
       outputType    = arrayOutputCType kind
       ownedLookup   = "sbv_array_owned_lookup_" ++ inputSuffix
       ownedRetain   = "sbv_array_owned_retain_" ++ inputSuffix
       ownedRelease  = "sbv_array_owned_release_" ++ inputSuffix
       keyType       = elementCType keyKind
       valueType     = elementCType valueKind
       hasExact      = isExactGMPKind cfg keyKind || isExactGMPKind cfg valueKind

       releaseManagedFields
         | keyManaged || valueManaged
         = ["  for (size_t i = 0; owner->nodes != NULL && i < owner->node_count; ++i) {"]
        ++ [ "    if (owner->nodes[i].kind == SBV_ARRAY_STORE) " ++ release "key" keyKind
           | keyManaged
           ]
        ++ [ "    if (owner->nodes[i].kind != SBV_ARRAY_CALLBACK) " ++ release "value" valueKind
           | valueManaged
           ]
        ++ ["  }"]
         | True
         = []

       keyManaged   = arrayFieldNeedsOwnership cfg keyKind
       valueManaged = arrayFieldNeedsOwnership cfg valueKind

       release field fieldKind = P.render $ managedValueRelease fieldKind (text ("&owner->nodes[i]." ++ field))

       cloneExact field fieldKind
         | isExactGMPKind cfg fieldKind
         = [ "      " ++ gmpOutputType fieldKind ++ " copy = " ++ gmpNewName fieldKind ++ "(&owner->exact_values);"
           , "      " ++ gmpFunctionName fieldKind "set" ++ "(copy, source->" ++ field ++ ");"
           , "      owner->nodes[i]." ++ field ++ " = copy;"
           ]
         | True
         = []

       cloneManaged field fieldKind
         | arrayFieldNeedsOwnership cfg fieldKind
         = [ "      owner->nodes[i]." ++ field ++ " = "
          ++ P.render (managedValueClone fieldKind (text ("source->" ++ field))) ++ ";"
           ]
         | True
         = []

ownershipRuntime _ kind = error $ "SBV->C: Expected an array kind, received " ++ show kind

-- | Materialize a borrowed public callback descriptor as an internal array
-- root. A null lookup callback is rejected before the symbolic program runs.
arrayInputSetup :: Int -> SV -> String -> [Doc]
arrayInputSetup typeWidth sv externalName
  | kind@KArray{} <- kindOf sv
  = [ text "if" P.<> parens (external P.<> text ".lookup == NULL") <+> text "abort" P.<> parens empty P.<> semi
    , text "if" P.<> parens (parens (external P.<> text ".retain == NULL") <+> text "!=" <+> parens (external P.<> text ".release == NULL")) <+> text "abort" P.<> parens empty P.<> semi
    , text "const" <+> text (arrayNodeType kind) <+> text nodeName <+> text "=" <+> braces (fsep (punctuate comma fields)) P.<> semi
    , text "const" <+> paddedType <+> text (show sv) <+> text "=" <+> text "&" P.<> text nodeName P.<> semi
    ]
 where external   = text externalName
       nodeName   = "sbv_local_array_input_" ++ show sv
       paddedType = text $ arrayCType (kindOf sv) ++ replicate (typeWidth - length (arrayCType (kindOf sv))) ' '
       fields     = [ text ".kind = SBV_ARRAY_CALLBACK"
                    , text ".lookup ="  <+> external P.<> text ".lookup"
                    , text ".context =" <+> external P.<> text ".context"
                    , text ".retain ="  <+> external P.<> text ".retain"
                    , text ".release =" <+> external P.<> text ".release"
                    ]
arrayInputSetup _ sv _ = error $ "SBV->C: Expected an array input, received " ++ show (kindOf sv)

-- | Emit the per-kind default-only callback used by example-driver array
-- values. Sharing one callback per array kind lets arrays appear at arbitrary
-- depth inside driver aggregates without requiring path-specific functions.
arrayDriverCallback :: CgConfig -> Kind -> Doc
arrayDriverCallback cfg kind@(KArray keyKind valueKind)
  = text "#ifndef" <+> text (arrayDriverGuard kind)
  $$ text "#define" <+> text (arrayDriverGuard kind)
  $$ text "static SBV_CGEN_UNUSED" <+> text (elementCType valueKind) <+> text callbackName
      P.<> parens (fsep (punctuate comma [text "const void *context", text (elementCType keyKind) <+> text "key"]))
  $$ text "{"
  $$ nest 2 (   parens (text "void") <+> text "key" P.<> semi
             $$ text "return" <+> result P.<> semi
            )
  $$ text "}"
  $$ text ""
  $$ retainContext
  $$ text ""
  $$ releaseContext
  $$ text "#endif"
 where callbackName = arrayDriverCallbackName kind
       retainName   = arrayDriverRetainName kind
       releaseName  = arrayDriverReleaseName kind
       result
         | isExactGMPKind cfg valueKind = parens (text (elementCType valueKind)) <+> text "context"
         | True                          = text "*" P.<> parens (parens (text (constElementCType valueKind) <+> text "*") <+> text "context")

       retainContext
         | isExactGMPKind cfg valueKind
         = text "static SBV_CGEN_UNUSED const void *" P.<> text retainName P.<> parens (text "const void *context")
           $$ text "{"
           $$ nest 2 (   text mutableType <+> text "copy =" <+> parens (text mutableType) <+> text "malloc(sizeof(*copy));"
                      $$ text "if (copy == NULL) abort();"
                      $$ vcat (map text exactCopy)
                      $$ text "return copy;"
                     )
           $$ text "}"
         | arrayFieldNeedsOwnership cfg valueKind
         = text "static SBV_CGEN_UNUSED const void *" P.<> text retainName P.<> parens (text "const void *context")
           $$ text "{"
           $$ nest 2 (   text (elementCType valueKind) <+> text "*copy =" <+> parens (text (elementCType valueKind) <+> text "*") <+> text "malloc(sizeof(*copy));"
                      $$ text "if (copy == NULL) abort();"
                      $$ text "*copy =" <+> managedValueClone valueKind managedContextValue P.<> semi
                      $$ text "return copy;"
                     )
           $$ text "}"
         | True
         = text "static SBV_CGEN_UNUSED const void *" P.<> text retainName P.<> parens (text "const void *context")
           $$ text "{"
           $$ nest 2 (   text (elementCType valueKind) <+> text "*copy =" <+> parens (text (elementCType valueKind) <+> text "*") <+> text "malloc(sizeof(*copy));"
                      $$ text "if (copy == NULL) abort();"
                      $$ text "*copy =" <+> managedContextValue P.<> semi
                      $$ text "return copy;"
                     )
           $$ text "}"

       releaseContext
         = text "static SBV_CGEN_UNUSED void" <+> text releaseName P.<> parens (text "const void *context")
           $$ text "{"
           $$ nest 2 (   managedClear
                      $$ exactClear
                      $$ text "free" P.<> parens (text "(void *) context") P.<> semi
                     )
           $$ text "}"

       managedContextValue = text "*" P.<> parens (parens (text (constElementCType valueKind) <+> text "*") <+> text "context")

       managedClear
         | arrayFieldNeedsOwnership cfg valueKind
         =  text (elementCType valueKind) <+> text "*value =" <+> parens (text (elementCType valueKind) <+> text "*") <+> text "context" P.<> semi
         $$ managedValueRelease valueKind (text "value")
         | True
         = empty

       mutableType
         | KUnbounded <- valueKind            = "mpz_ptr"
         | isExactGMPKind cfg valueKind        = "mpq_ptr"
         | True                                = error $ "SBV->C: Expected an exact callback value, received " ++ show valueKind

       exactCopy
         | KUnbounded <- valueKind = ["mpz_init_set(copy, (SInteger) context);"]
         | isExactGMPKind cfg valueKind
         = ["mpq_init(copy);", "mpq_set(copy, (" ++ elementCType valueKind ++ ") context);"]
         | True = error $ "SBV->C: Expected an exact callback value, received " ++ show valueKind

       exactClear
         | KUnbounded <- valueKind            = text "mpz_clear((mpz_ptr) context);"
         | isExactGMPKind cfg valueKind        = text "mpq_clear((mpq_ptr) context);"
         | True                                = empty
arrayDriverCallback _ kind = error $ "SBV->C: Expected an array input kind, received " ++ show kind

-- | Construct an example-driver descriptor around a named default value and
-- its generated callback. Exact GMP defaults already decay to pointers;
-- ordinary values are passed to the callback by address.
arrayDriverInput :: CgConfig -> Kind -> String -> String -> Doc
arrayDriverInput cfg kind inputName defaultName
  | KArray _ valueKind <- kind
  = let context
          | isExactGMPKind cfg valueKind = text defaultName
          | True                          = text "&" P.<> text defaultName
    in text "const" <+> text (arrayInputCType kind) <+> text inputName <+> text "="
         <+> braces (fsep (punctuate comma [ text ".lookup ="  <+> text (arrayDriverCallbackName kind)
                                          , text ".context =" <+> context
                                          , text ".retain ="  <+> text (arrayDriverRetainName kind)
                                          , text ".release =" <+> text (arrayDriverReleaseName kind)
                                          ])) P.<> semi
  | True
  = error $ "SBV->C: Expected an array input kind, received " ++ show kind

-- | Retain a generated input descriptor into the pointer representation used
-- by array-valued aggregate fields. The returned pointer owns both its heap
-- descriptor and one retained callback-context reference.
arrayDriverStoredInput :: Kind -> String -> String -> Doc
arrayDriverStoredInput kind@KArray{} externalName inputName
  =  text (arrayOutputCType kind) <+> text "*" P.<> text externalName <+> text "="
       <+> parens (text (arrayOutputCType kind) <+> text "*") <+> text "malloc(sizeof(*" P.<> text externalName P.<> text "));"
  $$ text "if" <+> parens (text externalName <+> text "== NULL") <+> text "abort();"
  $$ text "*" P.<> text externalName <+> text "="
       <+> text (arrayOutputRetainName kind)
       P.<> parens (parens (text (arrayOutputCType kind))
             <+> braces (fsep (punctuate comma [ text ".lookup ="  <+> text inputName P.<> text ".lookup"
                                               , text ".context =" <+> text inputName P.<> text ".context"
                                               , text ".retain ="  <+> text inputName P.<> text ".retain"
                                               , text ".release =" <+> text inputName P.<> text ".release"
                                               ]))) P.<> semi
arrayDriverStoredInput kind _ _ = error $ "SBV->C: Expected an array input kind, received " ++ show kind

-- | Render a concrete array model as a nested chain of C99 compound literals.
-- Association-list entries retain SBV's newest-write-first ordering.
arrayConst :: (CV -> Doc) -> CV -> Maybe Doc
arrayConst renderValue (CV kind@(KArray keyKind valueKind) (CArray (ArrayModel associations defaultValue)))
  = Just $ foldr store base associations
 where base = nodeLiteral [text ".kind = SBV_ARRAY_CONSTANT", text ".value =" <+> renderField valueKind defaultValue]

       store (key, value) parent = nodeLiteral
         [ text ".kind = SBV_ARRAY_STORE"
         , text ".parent =" <+> parent
         , text ".key ="    <+> renderValue (CV keyKind key)
         , text ".value ="  <+> renderField valueKind value
         ]

       renderField fieldKind fieldValue
         = arrayStoredValue fieldKind (renderValue (CV fieldKind fieldValue))

       nodeLiteral fields = parens $ text "&" P.<> parens (text (arrayNodeType kind)) P.<> braces (fsep (punctuate comma fields))
arrayConst _ _ = Nothing

-- | Lower array initialization, reads, writes, and array-valued conditionals.
-- Structured lambda-backed arrays, including free arrays, become callback
-- roots. Array-valued elements cross node boundaries through retained
-- descriptor pointers. The supplied name resolvers identify private defined
-- functions and lambda-lifted array callbacks. Equality calls a helper whose
-- finite key domain and enumeration limit are checked by the C renderer.
arrayExpr :: CgConfig
          -> (T.Text -> Maybe String)
          -> (SV -> Maybe String)
          -> Op
          -> [SV]
          -> SV
          -> [Doc]
          -> Maybe CLowering
arrayExpr cfg definedFunctionName structuredLambdaName op svs resultSV args
  | not (isArray resultKind || any isArray svs)
  = Nothing
  | True
  = case (op, svs, args) of
      (TupleConstructor{}, _, _) -> Nothing
      (TupleAccess{},      _, _) -> Nothing
      (ADTOp{},            _, _) -> Nothing
      (SeqOp{},            _, _) -> Nothing
      (SetOp{},            _, _) -> Nothing
      (LkUp{},             _, _) -> Nothing
      (Uninterpreted symbol, _, renderedArguments)
        | isArray resultKind
        , Just functionName <- definedFunctionName symbol
        -> Just $ arrayStoredLoad resultSV
             (namedCall functionName (text "&sbv_local_function_ctx" : renderedArguments))
        | True
        -> Nothing
      (ArrayInit (Left pair), [_], [defaultValue])
        | resultKind == uncurry KArray pair
        -> nodeLowering resultKind
             [text ".kind = SBV_ARRAY_CONSTANT", text ".value =" <+> storedValue (snd pair) defaultValue]
      (ArrayInit (Right lambdaDef), [], [])
        | Just _            <- smtLambdaInfo lambdaDef
        , Just callbackName <- structuredLambdaName resultSV
        -> nodeLowering resultKind
             [ text ".kind = SBV_ARRAY_CALLBACK"
             , text ".lookup ="  <+> text callbackName
             , text ".context =" <+> text "&sbv_local_function_ctx"
             , text ".retain ="  <+> text "sbv_function_ctx_retain_empty"
             , text ".release =" <+> text "sbv_function_ctx_release_owned"
             ]
        | True
        -> unsupported "lambda arrays without registered retained structured expressions"
      (ReadArray, [array, key], [renderedArray, renderedKey])
        | kindOf array == KArray (kindOf key) resultKind
        -> let readResult = namedCall (arrayReadName (kindOf array)) [renderedArray, renderedKey]
           in if isArray resultKind then Just (arrayStoredLoad resultSV readResult) else expression readResult
      (WriteArray, [array, key, value], [renderedArray, renderedKey, renderedValue])
        | resultKind == kindOf array
        , resultKind == KArray (kindOf key) (kindOf value)
        -> nodeLowering resultKind
             [ text ".kind = SBV_ARRAY_STORE"
             , text ".parent =" <+> renderedArray
             , text ".key ="    <+> renderedKey
             , text ".value ="  <+> storedValue (kindOf value) renderedValue
             ]
      (Label label, [_], [array])
        -> expression $ array <+> text "/*" <+> cCommentText label <+> text "*/"
      (Equal{}, initial:rest, a:as)
        | all ((== kindOf initial) . kindOf) rest
        -> expression $ conjunction [namedCall (arrayEqualName (kindOf initial)) [a, b] | b <- as]
      (NotEqual, initial:rest, _)
        | all ((== kindOf initial) . kindOf) rest
        -> expression $ conjunction [text "!" P.<> parens (namedCall (arrayEqualName (kindOf initial)) [a, b])
                                    | a:as <- tails args, b <- as]
      _                  -> error $ "SBV->C: Unsupported array operation " ++ show op
                           ++ " with argument kinds " ++ show (map kindOf svs)
                           ++ " and result kind " ++ show resultKind
 where resultKind = kindOf resultSV

       expression = Just . expressionLowering requirements

       conjunction [] = text "true"
       conjunction ds = hsep (punctuate (text " &&") (map parens ds))

       nodeLowering kind fields = Just CLowering
         { loweringExpression   = text "&" P.<> text nodeName
         , loweringDeclarations = [text (arrayNodeType kind) <+> text nodeName P.<> semi]
         , loweringSetup        = [text nodeName <+> text "=" <+> parens (text (arrayNodeType kind))
                                                    <+> braces (fsep (punctuate comma fields)) P.<> semi]
         , loweringRequirements = Set.fromList requirements
         }

       nodeName = "sbv_local_array_" ++ show resultSV

       storedValue = arrayStoredValue

       requirements = CRequiresArrays : concatMap kindRequirements (resultKind : map kindOf svs)

       kindRequirements kind
         | isWideBV kind                 = [CRequiresWideBV]
         | isFP kind                     = [CRequiresLibBF, CRequiresLibM]
         | isExactGMPKind cfg kind        = [CRequiresGMP]
         | kind `elem` [KFloat, KDouble] = [CRequiresLibM]
         | KArray keyKind valueKind <- kind
         = kindRequirements keyKind ++ kindRequirements valueKind
         | True = []

       unsupported feature = error $ "SBV->C: Arrays do not yet support " ++ feature ++ "."

       namedCall functionName callArgs = text functionName P.<> parens (fsep (punctuate comma callArgs))

-- | Name the private exact finite-domain array equality helper.
arrayEqualName :: Kind -> String
arrayEqualName kind = "sbv_array_equal_" ++ arraySuffix kind

-- | Initialize the arena that owns array descriptors embedded in temporary
-- generated values.
arrayContextStart :: Doc
arrayContextStart = text "sbv_array_ctx sbv_local_array_ctx = {NULL};"

-- | Release the array descriptors embedded in temporary generated values.
arrayContextEnd :: Doc
arrayContextEnd = text "sbv_array_ctx_end" P.<> parens (text "&sbv_local_array_ctx") P.<> semi

-- | Return the concrete node-structure name for an array kind.
arrayNodeType :: Kind -> String
arrayNodeType kind = "sbv_array_node_" ++ arraySuffix kind

-- | Return the lookup-helper name for an array kind.
arrayReadName :: Kind -> String
arrayReadName kind = "sbv_array_read_" ++ arraySuffix kind

-- | Return the callback-function-pointer type for an array kind.
arrayLookupType :: Kind -> String
arrayLookupType kind = "SBVArrayLookup_" ++ arraySuffix kind

-- | Return the generated example-driver callback name for an array kind.
arrayDriverCallbackName :: Kind -> String
arrayDriverCallbackName kind = "sbv_local_array_driver_lookup_" ++ arraySuffix kind

-- | Return the generated example-driver context-retain callback name.
arrayDriverRetainName :: Kind -> String
arrayDriverRetainName kind = "sbv_local_array_retain_driver_" ++ arraySuffix kind

-- | Return the generated example-driver context-release callback name.
arrayDriverReleaseName :: Kind -> String
arrayDriverReleaseName kind = "sbv_local_array_release_driver_" ++ arraySuffix kind

-- | Return the preprocessor guard that deduplicates a per-kind driver callback
-- when independently generated library components share an array type.
arrayDriverGuard :: Kind -> String
arrayDriverGuard kind = "SBV_ARRAY_DRIVER_CALLBACK_" ++ arraySuffix kind ++ "_DEFINED"

-- | Return the generated C lookup-helper name for a structured lambda array.
arrayLambdaName :: SV -> String
arrayLambdaName array = "sbv_array_lambda_" ++ show array

-- | Return the key/value suffix shared by the generated names for an array
-- kind.
arraySuffix :: Kind -> String
arraySuffix = arrayKindTag

-- | Return the preprocessor guard protecting an array type declaration.
arrayGuard :: Kind -> String
arrayGuard kind = arrayCType kind ++ "_DEFINED"

-- | Return the preprocessor guard protecting an array descriptor's forward
-- declaration and stored-value helper prototypes.
arrayForwardGuard :: Kind -> String
arrayForwardGuard kind = arrayOutputCType kind ++ "_FORWARD_DEFINED"

-- | Render the strong equality used to match array keys. Unlike IEEE numeric
-- equality, this recursively preserves object equality for aggregate fields.
keyEqual :: CgConfig -> Kind -> Doc -> Doc -> Doc
keyEqual cfg = byValueEqual cfg True

-- | Test whether an array field needs an independent deep copy when its node
-- escapes the generated call. Direct exact values use the owner's GMP arena.
arrayFieldNeedsOwnership :: CgConfig -> Kind -> Bool
arrayFieldNeedsOwnership cfg kind
  | isExactGMPKind cfg kind = False
  | isConcreteADT kind      = True
  | True                    = valueNeedsOwnership cfg kind
