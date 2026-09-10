-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.Set
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Finite and cofinite symbolic-set lowering for generated C.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.Set
  ( setKinds
  , setSupported
  , setUsesExact
  , setNeedsDriverInit
  , setCType
  , setForwardTypeDecls
  , setTypeDecls
  , setOwnershipTypeDecls
  , setRuntimeDecls
  , setRuntime
  , setConst
  , setExpr
  , setEqual
  , setNormalize
  , setClone
  , setRelease
  , setDriverValue
  , setDriverInit
  , setDriverClear
  , setPrint
  , setContextStart
  , setContextEnd
  ) where

import Data.Char                       (toUpper)
import Data.List                       (nub, stripPrefix, tails)
import qualified Data.Set as Set

import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as P ((<>))

import Data.SBV.Compilers.C.GMP        (isExactGMPKind)
import Data.SBV.Compilers.C.Lowering   (CLowering, CRequirement(..), CStorage(..), expressionLowering)
import Data.SBV.Compilers.C.Types      (elementCType, kindTag)
import Data.SBV.Compilers.C.Value      ( byValueEqual
                                       , managedValueClone
                                       , managedValueRelease
                                       , valueDriverClear
                                       , valueDriverInit
                                       , valueDriverNeedsInitialization
                                       , valueNeedsOwnership
                                       )
import Data.SBV.Compilers.CodeGen      (CgConfig)
import Data.SBV.Core.Data
import Data.SBV.Core.Kind              (expandKinds)
import Data.SBV.Core.Symbolic          (SetOp(..))

-- | Return all distinct symbolic-set kinds used by a program.
setKinds :: Set.Set Kind -> [Kind]
setKinds = nub . concatMap (filter isSet . expandKinds) . Set.toAscList

-- | Test whether a set element kind has a supported C representation.
setSupported :: CgConfig -> Kind -> Bool
setSupported _ (KSet elementKind) = supportedElement elementKind
 where supportedElement KBool          = True
       supportedElement KBounded{}     = True
       supportedElement KFloat         = True
       supportedElement KDouble        = True
       supportedElement KChar          = True
       supportedElement KString        = True
       supportedElement KFP{}          = True
       supportedElement KUnbounded     = True
       supportedElement KReal          = True
       supportedElement KRational      = True
       supportedElement (KList kind)   = supportedElement kind
       supportedElement (KTuple kinds) = all supportedElement kinds
       supportedElement kind
         | isConcreteADT kind = True
         | True               = isRoundingMode kind
setSupported _ _ = False

-- | Test whether a set stores exact GMP-backed elements.
setUsesExact :: CgConfig -> Kind -> Bool
setUsesExact cfg (KSet elementKind) = isExactGMPKind cfg elementKind
setUsesExact _   _                  = False

-- | Test whether an example-driver set requires statement-based element
-- initialization instead of a single compound literal.
setNeedsDriverInit :: CgConfig -> Kind -> Bool
setNeedsDriverInit cfg (KSet elementKind) = valueDriverNeedsInitialization cfg elementKind
setNeedsDriverInit _   _                  = False

-- | Return the public C descriptor type for a symbolic-set kind.
setCType :: Kind -> String
setCType kind@KSet{} = elementCType kind
setCType kind        = error $ "SBV->C: Expected a set kind, received " ++ show kind

-- | Emit guarded forward declarations for symbolic-set descriptor types.
-- These declarations allow set and list descriptors to contain pointers to
-- each other before either family has emitted its complete layouts.
setForwardTypeDecls :: [Kind] -> Doc
setForwardTypeDecls []    = empty
setForwardTypeDecls kinds = text . unlines $ concatMap declaration kinds
 where declaration kind@KSet{} =
         [ "#ifndef " ++ setForwardGuard kind
         , "#define " ++ setForwardGuard kind
         , "typedef struct " ++ setCType kind ++ " " ++ setCType kind ++ ";"
         , "#endif"
         , ""
         ]
       declaration kind = error $ "SBV->C: Expected a set kind, received " ++ show kind

-- | Emit finite/cofinite set descriptors and ownership-helper prototypes.
-- Aggregate element layouts may remain incomplete here; helper definitions
-- are emitted later by 'setOwnershipTypeDecls'.
setTypeDecls :: CgConfig -> [Kind] -> Doc
setTypeDecls cfg kinds
  | null kinds = empty
  | True       = setForwardTypeDecls kinds $$ text (unlines $
      ["/* Finite/cofinite symbolic sets. Inputs borrow elements; outputs and returns own them. */"
      , "#ifndef SBV_CGEN_UNUSED"
      , "#if defined(__GNUC__) || defined(__clang__)"
      , "#define SBV_CGEN_UNUSED __attribute__((unused))"
      , "#else"
      , "#define SBV_CGEN_UNUSED"
      , "#endif"
      , "#endif"
      ]
      ++ concatMap declaration kinds
      )
 where declaration kind@(KSet elementKind)
         | setSupported cfg kind
         = let cType       = setCType kind
               elementType = setElementCType elementKind
               cloneName    = setCloneName kind
               releaseName  = setReleaseName kind
           in [ "#ifndef " ++ setGuard kind
              , "#define " ++ setGuard kind
              , "struct " ++ cType ++ " { const " ++ elementType ++ " *data; size_t length; bool is_complement; };"
              , "static inline SBV_CGEN_UNUSED " ++ cType ++ " " ++ cloneName ++ "(" ++ cType ++ " value);"
              , "static inline SBV_CGEN_UNUSED void " ++ releaseName ++ "(" ++ cType ++ " *value);"
              , "#endif"
              , ""
              ]
         | True
         = error $ "SBV->C: Unsupported set element kind: " ++ show elementKind
       declaration kind = error $ "SBV->C: Expected a set kind, received " ++ show kind

-- | Emit set clone and release definitions after aggregate element layouts
-- are complete. Inputs borrow arrays that may contain duplicates; outputs and
-- returns own their cloned arrays.
setOwnershipTypeDecls :: CgConfig -> [Kind] -> Doc
setOwnershipTypeDecls cfg kinds
  | null kinds = empty
  | True       = text . unlines $ concatMap declaration kinds
 where declaration kind@(KSet elementKind)
         | setSupported cfg kind
         = let cType       = setCType kind
               elementType = setElementCType elementKind
               cloneName    = setCloneName kind
               releaseName  = setReleaseName kind
           in [ "#ifndef " ++ setOwnershipGuard kind
              , "#define " ++ setOwnershipGuard kind
              , "static inline SBV_CGEN_UNUSED " ++ cType ++ " " ++ cloneName ++ "(" ++ cType ++ " value)"
              , "{"
              , "  " ++ elementType ++ " *copy = NULL;"
              , "  if (value.length != 0) {"
              , "    if (value.length > SIZE_MAX / sizeof(*copy)) abort();"
              , "    copy = (" ++ elementType ++ " *) malloc(value.length * sizeof(*copy));"
              , "    if (copy == NULL) abort();"
              ]
              ++ cloneElements elementKind
              ++ [ "  }"
              , "  return (" ++ cType ++ ") {copy, value.length, value.is_complement};"
              , "}"
              , "static inline SBV_CGEN_UNUSED void " ++ releaseName ++ "(" ++ cType ++ " *value)"
              , "{"
              , "  if (value == NULL) return;"
              ]
              ++ releaseElements elementKind
              ++ [ "  *value = (" ++ cType ++ ") {NULL, 0, false};"
              , "}"
              , "#endif"
              , ""
              ]
         | True
         = error $ "SBV->C: Unsupported set element kind: " ++ show elementKind
       declaration kind = error $ "SBV->C: Expected a set kind, received " ++ show kind

       cloneElements elementKind
         | isExactGMPKind cfg elementKind
         =  [ "    for (size_t i = 0; i < value.length; ++i) {"
            , "      " ++ exactMutableType elementKind ++ " element = (" ++ exactMutableType elementKind ++ ") malloc(sizeof(*element));"
            , "      if (element == NULL) abort();"
            ]
         ++ exactInitialize elementKind
         ++ [ "      copy[i] = element;"
            , "    }"
            ]
         | isConcreteADT elementKind || valueNeedsOwnership cfg elementKind
         = [ "    for (size_t i = 0; i < value.length; ++i)"
           , "      copy[i] = " ++ render (managedValueClone elementKind (text "value.data[i]")) ++ ";"
           ]
         | True
         = ["    memcpy(copy, value.data, value.length * sizeof(*copy));"]

       releaseElements elementKind
         | isExactGMPKind cfg elementKind
         = [ "  " ++ setElementCType elementKind ++ " *data = (" ++ setElementCType elementKind ++ " *) value->data;"
           , "  for (size_t i = 0; i < value->length; ++i) {"
           , "    " ++ exactMutableType elementKind ++ " element = (" ++ exactMutableType elementKind ++ ") data[i];"
           , "    if (element != NULL) { " ++ exactClear elementKind ++ "(element); free(element); }"
           , "  }"
           , "  free(data);"
           ]
         | isConcreteADT elementKind || valueNeedsOwnership cfg elementKind
         = [ "  " ++ setElementCType elementKind ++ " *data = (" ++ setElementCType elementKind ++ " *) value->data;"
           , "  for (size_t i = 0; i < value->length; ++i)"
           , "    " ++ render (managedValueRelease elementKind (text "&data[i]"))
           , "  free(data);"
           ]
         | True
         = ["  free((void *) value->data);"]

       exactMutableType KUnbounded = "mpz_ptr"
       exactMutableType fieldKind
         | isExactGMPKind cfg fieldKind = "mpq_ptr"
       exactMutableType fieldKind = error $ "SBV->C: Expected an exact set element, received " ++ show fieldKind

       exactInitialize KUnbounded = ["      mpz_init_set(element, value.data[i]);"]
       exactInitialize fieldKind
         | isExactGMPKind cfg fieldKind
         = [ "      mpq_init(element);"
           , "      mpq_set(element, value.data[i]);"
           ]
       exactInitialize fieldKind = error $ "SBV->C: Expected an exact set element, received " ++ show fieldKind

       exactClear KUnbounded = "mpz_clear"
       exactClear fieldKind
         | isExactGMPKind cfg fieldKind = "mpq_clear"
       exactClear fieldKind = error $ "SBV->C: Expected an exact set element, received " ++ show fieldKind

-- | Emit forward declarations for set equality helpers referenced by nested
-- aggregate element comparisons.
setRuntimeDecls :: CgConfig -> [Kind] -> Doc
setRuntimeDecls cfg kinds = text . unlines $
  [ "static SBV_CGEN_UNUSED bool " ++ helperName kind "equal" ++ "(" ++ setCType kind ++ " left, " ++ setCType kind ++ " right);"
  | kind <- kinds
  , setSupported cfg kind
  ]

-- | Emit the shared set arena and one operation family per element kind.
setRuntime :: CgConfig -> [Kind] -> Doc
setRuntime cfg kinds = text . unlines . map markUnused $ commonRuntime ++ concatMap specializedRuntime kinds
 where markUnused line = case stripPrefix "static " line of
                           Just rest -> "static SBV_CGEN_UNUSED " ++ rest
                           Nothing   -> line

       specializedRuntime kind
         | setSupported cfg kind = setKindRuntime cfg kind
         | True                  = error $ "SBV->C: Unsupported set kind: " ++ show kind

-- | Render a regular or complemented set constant.
setConst :: (CV -> Doc) -> CV -> Maybe Doc
setConst renderElement (CV kind@(KSet elementKind) (CSet value))
  = Just $ text "((" P.<> text (setCType kind) P.<> text ") {"
       P.<> elements
       P.<> text ", "
       P.<> int (length values)
       P.<> text ", "
       P.<> text (if isComplement then "true" else "false")
       P.<> text "})"
 where (isComplement, stored) = case value of
                                  RegularSet entries    -> (False, entries)
                                  ComplementSet entries -> (True,  entries)
       values = Set.toAscList stored
       elements
         | null values = text "NULL"
         | True        = text "(const" <+> text (setElementCType elementKind) P.<> text "[]) {"
                      P.<> fsep (punctuate comma (map (renderElement . CV elementKind) values))
                      P.<> text "}"
setConst _ _ = Nothing

-- | Lower symbolic set construction, membership, comparison, and algebra.
setExpr :: CgConfig -> Op -> [SV] -> Kind -> [Doc] -> Maybe CLowering
setExpr cfg op svs resultKind args
  | not touchesSet = Nothing
  | True           = case (op, args) of
      (ADTOp{}                       , _        ) -> Nothing
      (TupleConstructor{}            , _        ) -> Nothing
      (TupleAccess{}                 , _        ) -> Nothing
      (Label _                       , [a]      ) -> lower a
      (Ite                           , [c, a, b]) -> lower $ c <+> text "?" <+> a <+> text ":" <+> b
      (Equal _                       , [a, b]   ) -> lower $ call (helper "equal") [a, b]
      (NotEqual                      , as       ) -> lower $ distinctSets as
      (SetOp SetEqual                , [a, b]   ) -> lower $ call (helper "equal") [a, b]
      (SetOp SetMember               , [e, s]   ) -> lower $ call (helper "member") [e, s]
      (SetOp SetInsert               , [e, s]   ) -> lower $ arenaCall "insert" [e, s]
      (SetOp SetDelete               , [e, s]   ) -> lower $ arenaCall "delete" [e, s]
      (SetOp SetIntersect            , [a, b]   ) -> lower $ arenaCall "intersection" [a, b]
      (SetOp SetUnion                , [a, b]   ) -> lower $ arenaCall "union" [a, b]
      (SetOp SetSubset               , [a, b]   ) -> lower $ call (helper "subset") [a, b]
      (SetOp SetDifference           , [a, b]   ) -> lower $ arenaCall "difference" [a, b]
      (SetOp SetComplement           , [a]      ) -> lower $ call (helper "complement") [a]
      _ -> unsupported
 where touchesSet = isSet resultKind || any (isSet . kindOf) svs || isSetOp op

       setKind = case [kind | value <- resultKind : map kindOf svs, kind@(KSet _) <- [value]] of
                   kind : _ -> kind
                   []       -> error $ "SBV->C: Cannot determine set kind for " ++ show op

       lower expression = Just $ expressionLowering storage requirements expression

       requirements = CRequiresSets : [CRequiresGMP | any (isExactGMPKind cfg) touchedKinds]

       touchedKinds = concatMap expandKinds (resultKind : map kindOf svs)

       storage
         | isSet resultKind = CFunctionScoped
         | True             = CByValue

       helper = helperName setKind

       arenaCall suffix rendered = call (helper suffix) (text "&__sbv_set_ctx" : rendered)

       distinctSets rendered = fsep $ punctuate (text " &&")
                                     [parens (text "!" P.<> call (helper "equal") [left, right])
                                     | left : rest <- tails rendered, right <- rest]

       unsupported = error $ "SBV->C: Set lowering does not support " ++ show op
                          ++ " with argument kinds " ++ show (map kindOf svs)
                          ++ " and result kind " ++ show resultKind

-- | Compare two set descriptors using finite/cofinite symbolic-set equality.
setEqual :: Kind -> Doc -> Doc -> Doc
setEqual kind left right = call (helperName kind "equal") [left, right]

-- | Normalize a borrowed set descriptor into the generated function's arena.
setNormalize :: Kind -> Doc -> Doc
setNormalize kind value = call (helperName kind "normalize") [text "&__sbv_set_ctx", value]

-- | Deep-copy a set across the generated function's ownership boundary.
setClone :: Kind -> Doc -> Doc
setClone kind value = call (setCloneName kind) [value]

-- | Release an owned set in a generated driver.
setRelease :: Kind -> Doc -> Doc
setRelease kind value = call (setReleaseName kind) [text "&" P.<> value] P.<> semi

-- | Produce a deterministic three-element finite or cofinite driver value.
setDriverValue :: (Kind -> Integer -> Doc) -> Kind -> Integer -> Doc
setDriverValue renderValue kind@(KSet elementKind) seed
  = text "((" P.<> text (setCType kind) P.<> text ") {"
       P.<> text "(const" <+> text (setElementCType elementKind) P.<> text "[]) {"
       P.<> fsep (punctuate comma [renderValue elementKind seed, renderValue elementKind (seed + 1), renderValue elementKind (seed + 2)])
       P.<> text "}, 3, "
       P.<> text (if odd seed then "true" else "false")
       P.<> text "})"
setDriverValue _ kind _ = error $ "SBV->C: Expected a set kind, received " ++ show kind

-- | Initialize a generated-driver set whose elements require statement-based
-- setup. The descriptor borrows three independently initialized elements and
-- uses the sample seed's parity to choose a finite or cofinite representation.
-- The supplied statement renderer handles retained array elements when the
-- element kind admits executable equality.
setDriverInit :: CgConfig -> (Kind -> Integer -> Doc) -> (Kind -> String -> Integer -> Doc) -> Kind -> String -> Integer -> Doc
setDriverInit cfg renderValue initializeArray kind@KSet{} externalName seed = valueDriverInit cfg renderValue initializeArray kind externalName seed
setDriverInit _   _           _               kind        _            _    = error $ "SBV->C: Expected a set kind, received " ++ show kind

-- | Clear managed element storage initialized by 'setDriverInit'.
setDriverClear :: CgConfig -> Kind -> String -> Doc
setDriverClear cfg kind@KSet{} externalName = valueDriverClear cfg kind externalName
setDriverClear _   kind        _            = error $ "SBV->C: Expected a set kind, received " ++ show kind

-- | Print a finite set as @{...}@ and a cofinite set as @U - {...}@.
setPrint :: (Kind -> Doc -> Doc) -> Kind -> Doc -> Doc
setPrint printElement (KSet elementKind) value
  = text "if" P.<> parens (value P.<> text ".is_complement") <+> text "printf(\"U\");"
 $$ text "if" P.<> parens (text "!" P.<> value P.<> text ".is_complement ||" <+> value P.<> text ".length != 0")
 $$ text "{"
 $$ nest 2 (   text "if" P.<> parens (value P.<> text ".is_complement") <+> text "printf(\" - \");"
            $$ text "printf(\"{\");"
            $$ text "for (size_t" <+> index <+> text "= 0;" <+> index <+> text "<" <+> value P.<> text ".length; ++" P.<> index P.<> text ")"
            $$ text "{"
            $$ nest 2 (   text "if" <+> parens (index <+> text "!= 0") <+> text "printf(\", \");"
                       $$ printElement elementKind (value P.<> text ".data[" P.<> index P.<> text "]")
                      )
            $$ text "}"
            $$ text "printf(\"}\");"
           )
 $$ text "}"
 where index = text ("__sbv_set_print_index_" ++ kindTag elementKind)
setPrint _ kind _ = error $ "SBV->C: Expected a set kind, received " ++ show kind

-- | Initialize the arena used by set temporaries in a generated function.
setContextStart :: Doc
setContextStart = text "sbv_set_ctx __sbv_set_ctx = {NULL};"

-- | Release all set temporaries allocated by a generated function.
setContextEnd :: Doc
setContextEnd = call "sbv_set_ctx_end" [text "&__sbv_set_ctx"] P.<> semi

-- | Test whether an operation belongs to the symbolic-set family.
isSetOp :: Op -> Bool
isSetOp SetOp{} = True
isSetOp _       = False

-- | Return the element kind of a symbolic-set kind.
setElementKind :: Kind -> Kind
setElementKind (KSet elementKind) = elementKind
setElementKind kind               = error $ "SBV->C: Expected a set kind, received " ++ show kind

-- | Return the public C type used for one supported set element.
setElementCType :: Kind -> String
setElementCType KChar = "SChar"
setElementCType kind  = elementCType kind

-- | Return the collision-free tag used for one supported set element.
setElementTag :: Kind -> String
setElementTag KChar = "char"
setElementTag kind  = kindTag kind

-- | Return the preprocessor guard for one set forward declaration.
setForwardGuard :: Kind -> String
setForwardGuard kind = "SBV_SET_" ++ map toUpper (setElementTag (setElementKind kind)) ++ "_FORWARD_DEFINED"

-- | Return the preprocessor guard for one set descriptor.
setGuard :: Kind -> String
setGuard kind = "SBV_SET_" ++ map toUpper (setElementTag (setElementKind kind)) ++ "_DEFINED"

-- | Return the preprocessor guard for one set ownership-helper definition.
setOwnershipGuard :: Kind -> String
setOwnershipGuard kind = "SBV_SET_" ++ map toUpper (setElementTag (setElementKind kind)) ++ "_OWNERSHIP_DEFINED"

-- | Return the generated clone-helper name for a set kind.
setCloneName :: Kind -> String
setCloneName kind = "sbv_set_clone_" ++ setElementTag (setElementKind kind)

-- | Return the generated release-helper name for a set kind.
setReleaseName :: Kind -> String
setReleaseName kind = "sbv_set_release_" ++ setElementTag (setElementKind kind)

-- | Return one specialized set-operation helper name.
helperName :: Kind -> String -> String
helperName kind suffix = "sbv_set_" ++ setElementTag (setElementKind kind) ++ "_" ++ suffix

-- | Render a C helper call.
call :: String -> [Doc] -> Doc
call functionName args = text functionName P.<> parens (fsep (punctuate comma args))

-- | Shared per-call allocation arena used by every set specialization.
commonRuntime :: [String]
commonRuntime =
  ["/* Per-call ownership arena for symbolic-set temporaries. */"
  , "typedef struct sbv_set_node { struct sbv_set_node *next; long double data[]; } sbv_set_node;"
  , "typedef struct { sbv_set_node *head; } sbv_set_ctx;"
  , "static void *sbv_set_alloc(sbv_set_ctx *ctx, size_t count, size_t element_size)"
  , "{"
  , "  if (count == 0) return NULL;"
  , "  if (element_size == 0 || count > SIZE_MAX / element_size) abort();"
  , "  const size_t bytes = count * element_size;"
  , "  if (bytes > SIZE_MAX - sizeof(sbv_set_node)) abort();"
  , "  sbv_set_node *node = (sbv_set_node *) malloc(sizeof(*node) + bytes);"
  , "  if (node == NULL) abort();"
  , "  node->next = ctx->head; ctx->head = node; return node->data;"
  , "}"
  , "static void sbv_set_ctx_end(sbv_set_ctx *ctx)"
  , "{"
  , "  while (ctx->head != NULL) {"
  , "    sbv_set_node *next = ctx->head->next; free(ctx->head); ctx->head = next;"
  , "  }"
  , "}"
  ]

-- | Emit all set helpers for one supported element kind.
setKindRuntime :: CgConfig -> Kind -> [String]
setKindRuntime cfg kind@(KSet elementKind) =
  [ ""
  , "static bool " ++ equalElement ++ "(" ++ elementType ++ " left, " ++ elementType ++ " right)"
  , "{ return " ++ elementEqual ++ "; }"
  , "static bool " ++ helper "stored_contains" ++ "(" ++ setType ++ " value, " ++ elementType ++ " element)"
  , "{"
  , "  for (size_t i = 0; i < value.length; ++i) if (" ++ equalElement ++ "(value.data[i], element)) return true;"
  , "  return false;"
  , "}"
  , "static " ++ setType ++ " " ++ helper "normalize" ++ "(sbv_set_ctx *ctx, " ++ setType ++ " value)"
  , "{"
  , "  " ++ elementType ++ " *data = (" ++ elementType ++ " *) sbv_set_alloc(ctx, value.length, sizeof(*data));"
  , "  " ++ setType ++ " result = (" ++ setType ++ ") {data, 0, value.is_complement};"
  , "  for (size_t i = 0; i < value.length; ++i) if (!" ++ helper "stored_contains" ++ "(result, value.data[i])) data[result.length++] = value.data[i];"
  , "  return result;"
  , "}"
  , "static bool " ++ helper "stored_subset" ++ "(" ++ setType ++ " left, " ++ setType ++ " right)"
  , "{"
  , "  for (size_t i = 0; i < left.length; ++i) if (!" ++ helper "stored_contains" ++ "(right, left.data[i])) return false;"
  , "  return true;"
  , "}"
  , "static bool " ++ helper "stored_disjoint" ++ "(" ++ setType ++ " left, " ++ setType ++ " right)"
  , "{"
  , "  for (size_t i = 0; i < left.length; ++i) if (" ++ helper "stored_contains" ++ "(right, left.data[i])) return false;"
  , "  return true;"
  , "}"
  ]
  ++ storedRuntime
  ++ domainRuntime
  ++ [ "static bool " ++ helper "equal" ++ "(" ++ setType ++ " left, " ++ setType ++ " right)"
     , "{"
     , "  if (left.is_complement == right.is_complement) return " ++ helper "stored_subset" ++ "(left, right) && " ++ helper "stored_subset" ++ "(right, left);"
     , "  return " ++ helper "stored_disjoint" ++ "(left, right) && " ++ helper "domain_covered" ++ "(left, right);"
     , "}"
     , "static bool " ++ helper "member" ++ "(" ++ elementType ++ " element, " ++ setType ++ " value)"
     , "{ return value.is_complement != " ++ helper "stored_contains" ++ "(value, element); }"
     , "static " ++ setType ++ " " ++ helper "insert" ++ "(sbv_set_ctx *ctx, " ++ elementType ++ " element, " ++ setType ++ " value)"
     , "{"
     , "  const bool stored = " ++ helper "stored_contains" ++ "(value, element);"
     , "  if ((!value.is_complement && stored) || (value.is_complement && !stored)) return value;"
     , "  if (value.is_complement) return " ++ helper "stored_remove" ++ "(ctx, value, element, true);"
     , "  return " ++ helper "stored_add" ++ "(ctx, value, element, false);"
     , "}"
     , "static " ++ setType ++ " " ++ helper "delete" ++ "(sbv_set_ctx *ctx, " ++ elementType ++ " element, " ++ setType ++ " value)"
     , "{"
     , "  const bool stored = " ++ helper "stored_contains" ++ "(value, element);"
     , "  if ((!value.is_complement && !stored) || (value.is_complement && stored)) return value;"
     , "  if (value.is_complement) return " ++ helper "stored_add" ++ "(ctx, value, element, true);"
     , "  return " ++ helper "stored_remove" ++ "(ctx, value, element, false);"
     , "}"
     , "static " ++ setType ++ " " ++ helper "union" ++ "(sbv_set_ctx *ctx, " ++ setType ++ " left, " ++ setType ++ " right)"
     , "{"
     , "  if (!left.is_complement && !right.is_complement) return " ++ helper "stored_union" ++ "(ctx, left, right, false);"
     , "  if (!left.is_complement &&  right.is_complement) return " ++ helper "stored_difference" ++ "(ctx, right, left, true);"
     , "  if ( left.is_complement && !right.is_complement) return " ++ helper "stored_difference" ++ "(ctx, left, right, true);"
     , "  return " ++ helper "stored_intersection" ++ "(ctx, left, right, true);"
     , "}"
     , "static " ++ setType ++ " " ++ helper "intersection" ++ "(sbv_set_ctx *ctx, " ++ setType ++ " left, " ++ setType ++ " right)"
     , "{"
     , "  if (!left.is_complement && !right.is_complement) return " ++ helper "stored_intersection" ++ "(ctx, left, right, false);"
     , "  if (!left.is_complement &&  right.is_complement) return " ++ helper "stored_difference" ++ "(ctx, left, right, false);"
     , "  if ( left.is_complement && !right.is_complement) return " ++ helper "stored_difference" ++ "(ctx, right, left, false);"
     , "  return " ++ helper "stored_union" ++ "(ctx, left, right, true);"
     , "}"
     , "static " ++ setType ++ " " ++ helper "difference" ++ "(sbv_set_ctx *ctx, " ++ setType ++ " left, " ++ setType ++ " right)"
     , "{"
     , "  if (!left.is_complement && !right.is_complement) return " ++ helper "stored_difference" ++ "(ctx, left, right, false);"
     , "  if (!left.is_complement &&  right.is_complement) return " ++ helper "stored_intersection" ++ "(ctx, left, right, false);"
     , "  if ( left.is_complement && !right.is_complement) return " ++ helper "stored_union" ++ "(ctx, left, right, true);"
     , "  return " ++ helper "stored_difference" ++ "(ctx, right, left, false);"
     , "}"
     , "static " ++ setType ++ " " ++ helper "complement" ++ "(" ++ setType ++ " value)"
     , "{ value.is_complement = !value.is_complement; return value; }"
     , "static bool " ++ helper "subset" ++ "(" ++ setType ++ " left, " ++ setType ++ " right)"
     , "{"
     , "  if (!left.is_complement && !right.is_complement) return " ++ helper "stored_subset" ++ "(left, right);"
     , "  if (!left.is_complement &&  right.is_complement) return " ++ helper "stored_disjoint" ++ "(left, right);"
     , "  if ( left.is_complement && !right.is_complement) return " ++ helper "domain_covered" ++ "(left, right);"
     , "  return " ++ helper "stored_subset" ++ "(right, left);"
     , "}"
     ]
 where setType      = setCType kind
       elementType  = setElementCType elementKind
       helper       = helperName kind
       equalElement = helper "element_equal"

       elementEqual = render $ byValueEqual cfg True elementKind (text "left") (text "right")

       domainRuntime =
         [ "static bool " ++ helper "domain_covered" ++ "(" ++ setType ++ " left, " ++ setType ++ " right)"
         , "{"
         ]
         ++ case elementDomainSize elementKind of
              Nothing -> [ "  (void) left; (void) right; return false;" ]
              Just domainSize ->
                [ "  const uint64_t domain_size = UINT64_C(" ++ show domainSize ++ ");"
                , "  if (domain_size > (uint64_t) SIZE_MAX) return false;"
                , "  size_t covered = 0;"
                , "  for (size_t i = 0; i < left.length; ++i) {"
                , "    bool duplicate = false;"
                , "    for (size_t j = 0; j < i; ++j) if (" ++ equalElement ++ "(left.data[i], left.data[j])) { duplicate = true; break; }"
                , "    if (!duplicate) ++covered;"
                , "  }"
                , "  for (size_t i = 0; i < right.length; ++i) {"
                , "    bool duplicate = " ++ helper "stored_contains" ++ "(left, right.data[i]);"
                , "    for (size_t j = 0; !duplicate && j < i; ++j) duplicate = " ++ equalElement ++ "(right.data[i], right.data[j]);"
                , "    if (!duplicate) ++covered;"
                , "  }"
                , "  return (uint64_t) covered == domain_size;"
                ]
         ++ [ "}" ]

       storedRuntime =
         [ "static " ++ setType ++ " " ++ helper "stored_add" ++ "(sbv_set_ctx *ctx, " ++ setType ++ " value, " ++ elementType ++ " element, bool is_complement)"
         , "{"
         , "  if (value.length == SIZE_MAX) abort();"
         , "  " ++ elementType ++ " *data = (" ++ elementType ++ " *) sbv_set_alloc(ctx, value.length + 1, sizeof(*data));"
         , "  if (value.length != 0) memcpy(data, value.data, value.length * sizeof(*data));"
         , "  data[value.length] = element; return (" ++ setType ++ ") {data, value.length + 1, is_complement};"
         , "}"
         , "static " ++ setType ++ " " ++ helper "stored_remove" ++ "(sbv_set_ctx *ctx, " ++ setType ++ " value, " ++ elementType ++ " element, bool is_complement)"
         , "{"
         , "  const size_t length = value.length - 1;"
         , "  " ++ elementType ++ " *data = (" ++ elementType ++ " *) sbv_set_alloc(ctx, length, sizeof(*data));"
         , "  size_t output = 0;"
         , "  for (size_t i = 0; i < value.length; ++i) if (!" ++ equalElement ++ "(value.data[i], element)) data[output++] = value.data[i];"
         , "  return (" ++ setType ++ ") {data, length, is_complement};"
         , "}"
         , "static " ++ setType ++ " " ++ helper "stored_union" ++ "(sbv_set_ctx *ctx, " ++ setType ++ " left, " ++ setType ++ " right, bool is_complement)"
         , "{"
         , "  if (right.length > SIZE_MAX - left.length) abort();"
         , "  " ++ elementType ++ " *data = (" ++ elementType ++ " *) sbv_set_alloc(ctx, left.length + right.length, sizeof(*data));"
         , "  " ++ setType ++ " result = (" ++ setType ++ ") {data, 0, is_complement};"
         , "  for (size_t i = 0; i < left.length; ++i) data[result.length++] = left.data[i];"
         , "  for (size_t i = 0; i < right.length; ++i) if (!" ++ helper "stored_contains" ++ "(result, right.data[i])) data[result.length++] = right.data[i];"
         , "  return result;"
         , "}"
         , "static " ++ setType ++ " " ++ helper "stored_intersection" ++ "(sbv_set_ctx *ctx, " ++ setType ++ " left, " ++ setType ++ " right, bool is_complement)"
         , "{"
         , "  " ++ elementType ++ " *data = (" ++ elementType ++ " *) sbv_set_alloc(ctx, left.length, sizeof(*data));"
         , "  " ++ setType ++ " result = (" ++ setType ++ ") {data, 0, is_complement};"
         , "  for (size_t i = 0; i < left.length; ++i) if (" ++ helper "stored_contains" ++ "(right, left.data[i])) data[result.length++] = left.data[i];"
         , "  return result;"
         , "}"
         , "static " ++ setType ++ " " ++ helper "stored_difference" ++ "(sbv_set_ctx *ctx, " ++ setType ++ " left, " ++ setType ++ " right, bool is_complement)"
         , "{"
         , "  " ++ elementType ++ " *data = (" ++ elementType ++ " *) sbv_set_alloc(ctx, left.length, sizeof(*data));"
         , "  " ++ setType ++ " result = (" ++ setType ++ ") {data, 0, is_complement};"
         , "  for (size_t i = 0; i < left.length; ++i) if (!" ++ helper "stored_contains" ++ "(right, left.data[i])) data[result.length++] = left.data[i];"
         , "  return result;"
         , "}"
         ]
setKindRuntime _ kind = error $ "SBV->C: Expected a set kind, received " ++ show kind

-- | Test whether a kind is a concrete user ADT supported as a collection
-- element.
isConcreteADT :: Kind -> Bool
isConcreteADT kind = isADT kind && not (isRoundingMode kind) && not (isUninterpreted kind)

-- | Return the number of distinct SMT objects when the domain cardinality fits
-- in a C @uint64_t@. 'Nothing' means opposite finite/cofinite forms cannot be
-- proven equal from a representable C descriptor.
elementDomainSize :: Kind -> Maybe Integer
elementDomainSize KBool              = Just 2
elementDomainSize (KBounded _ width)
  | width < 64                       = Just (2 ^ width)
  | True                             = Nothing
elementDomainSize KFloat             = Just (2 ^ (32 :: Int) - 2 ^ (24 :: Int) + 3)
elementDomainSize KDouble            = Just (2 ^ (64 :: Int) - 2 ^ (53 :: Int) + 3)
elementDomainSize KChar              = Just 0x30000
elementDomainSize (KFP eb sb)
  | eb + sb <= 64                    = Just (2 ^ (eb + sb) - 2 ^ sb + 3)
  | True                             = Nothing
elementDomainSize (KTuple kinds)     = do
  sizes <- mapM elementDomainSize kinds
  let total = product sizes
  if total <= 2 ^ (64 :: Int) - 1 then Just total else Nothing
elementDomainSize kind@(KADT _ _ constructors)
  | isConcreteADT kind
  , all (null . snd) constructors     = Just (fromIntegral (length constructors))
elementDomainSize kind
  | isRoundingMode kind              = Just 5
  | True                             = Nothing
