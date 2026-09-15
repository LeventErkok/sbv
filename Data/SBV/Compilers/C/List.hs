-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.List
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Typed symbolic-list lowering for generated C.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.List
  ( listKinds
  , listSupported
  , listUsesExact
  , listNeedsDriverInit
  , listCType
  , listForwardTypeDecls
  , listTypeDecls
  , listOwnershipTypeDecls
  , listRuntimeDecls
  , listRuntime
  , listConst
  , listExpr
  , listEqual
  , listClone
  , listRelease
  , listDriverValue
  , listDriverInit
  , listDriverClear
  , listPrint
  , listContextStart
  , listContextEnd
  ) where

import Data.SBV.Compilers.C.Syntax (cUnusedAttribute)
import Data.List                       (nub, sortOn, stripPrefix, tails)
import qualified Data.Set as Set

import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as P ((<>))

import Data.SBV.Compilers.C.Arena      (CArena(..), arenaRuntime)
import Data.SBV.Compilers.C.Array      (arrayStoredLoad, arrayStoredValue)
import Data.SBV.Compilers.C.GMP        (gmpFunctionName, gmpInitializeCopy, gmpOutputType, isExactGMPKind)
import Data.SBV.Compilers.C.Lowering   (CLowering, CRequirement(..), expressionLowering)
import Data.SBV.Compilers.C.Types      (isConcreteADT, constElementCType, elementCType, kindTag, listCloneName, listReleaseName, listHelperName)
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

-- | Return all distinct symbolic-list kinds in dependency order.
listKinds :: Set.Set Kind -> [Kind]
listKinds = sortOn listDepth . nub . concatMap (filter isList . expandKinds) . Set.toAscList
 where listDepth :: Kind -> Int
       listDepth (KList elementKind) = 1 + listDepth elementKind
       listDepth _                   = 0

-- | Test whether a list element kind has a supported C representation. Array
-- elements support structural movement and indexing, but operations requiring
-- extensional element equality are rejected by 'listExpr'.
listSupported :: CgConfig -> Kind -> Bool
listSupported _ (KList elementKind) = supportedElement elementKind
 where supportedElement KBool                          = True
       supportedElement KBounded{}                     = True
       supportedElement KFloat                         = True
       supportedElement KDouble                        = True
       supportedElement KChar                          = True
       supportedElement KString                        = True
       supportedElement KFP{}                          = True
       supportedElement KUnbounded                     = True
       supportedElement KReal                          = True
       supportedElement KRational                      = True
       supportedElement (KList kind)                   = supportedElement kind
       supportedElement (KSet kind)                    = supportedElement kind
       supportedElement (KArray keyKind valueKind)     = supportedElement keyKind && supportedElement valueKind
       supportedElement (KTuple kinds)                 = all supportedElement kinds
       supportedElement kind
         | isConcreteADT kind = True
         | True               = isRoundingMode kind
listSupported _ _ = False

-- | Test whether a list stores exact GMP-backed elements.
listUsesExact :: CgConfig -> Kind -> Bool
listUsesExact cfg (KList elementKind) = isExactGMPKind cfg elementKind
listUsesExact _   _                   = False

-- | Test whether an example-driver list requires statement-based element
-- initialization instead of a single compound literal.
listNeedsDriverInit :: CgConfig -> Kind -> Bool
listNeedsDriverInit cfg (KList elementKind) = valueDriverNeedsInitialization cfg elementKind
listNeedsDriverInit _   _                   = False

-- | Return the public C descriptor type for a symbolic-list kind.
listCType :: Kind -> String
listCType kind@KList{} = elementCType kind
listCType kind         = error $ "SBV->C: Expected a list kind, received " ++ show kind

-- | Emit guarded forward declarations for symbolic-list descriptor types.
-- These declarations allow list and set descriptors to contain pointers to
-- each other before either family has emitted its complete layouts.
listForwardTypeDecls :: [Kind] -> Doc
listForwardTypeDecls []    = empty
listForwardTypeDecls kinds = text . unlines $ concatMap declaration kinds
 where declaration kind@KList{} =
         [ "#ifndef " ++ listForwardGuard kind
         , "#define " ++ listForwardGuard kind
         , "typedef struct " ++ listCType kind ++ " " ++ listCType kind ++ ";"
         , "#endif"
         , ""
         ]
       declaration kind = error $ "SBV->C: Expected a list kind, received " ++ show kind

-- | Emit typed borrowed-list descriptors and ownership-helper prototypes.
-- The element type may remain incomplete here because descriptors only carry
-- pointers; definitions that inspect elements are emitted later by
-- 'listOwnershipTypeDecls'.
listTypeDecls :: CgConfig -> [Kind] -> Doc
listTypeDecls cfg kinds
  | null kinds = empty
  | True       = listForwardTypeDecls kinds $$ text (unlines $
      ["/* Typed symbolic lists. Inputs borrow their elements; outputs and returns own them. */"
      , cUnusedAttribute
      ]
      ++ concatMap declaration kinds
      )
 where declaration kind@(KList elementKind)
         | listSupported cfg kind
         = let cType       = listCType kind
               cloneName    = listCloneName kind
               releaseName  = listReleaseName kind
           in [ "#ifndef " ++ listGuard kind
              , "#define " ++ listGuard kind
              , "struct " ++ cType ++ " { " ++ constElementCType elementKind ++ " *data; size_t length; };"
              , "static inline SBV_CGEN_UNUSED " ++ cType ++ " " ++ cloneName ++ "(" ++ cType ++ " value);"
              , "static inline SBV_CGEN_UNUSED void " ++ releaseName ++ "(" ++ cType ++ " *value);"
              , "#endif"
              , ""
              ]
         | True
         = error $ "SBV->C: Unsupported list element kind: " ++ show elementKind
       declaration kind = error $ "SBV->C: Expected a list kind, received " ++ show kind

-- | Emit list clone and release definitions after aggregate element layouts
-- are complete. Inputs borrow their element arrays; output and return values
-- own a cloned array and must be released with the matching helper.
listOwnershipTypeDecls :: CgConfig -> [Kind] -> Doc
listOwnershipTypeDecls cfg kinds
  | null kinds = empty
  | True       = text . unlines $ concatMap declaration kinds
 where declaration kind@(KList elementKind)
         | listSupported cfg kind
         = let cType       = listCType kind
               elementType = listElementCType elementKind
               cloneName    = listCloneName kind
               releaseName  = listReleaseName kind
           in [ "#ifndef " ++ listOwnershipGuard kind
              , "#define " ++ listOwnershipGuard kind
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
              , "  return (" ++ cType ++ ") {copy, value.length};"
              , "}"
              , "static inline SBV_CGEN_UNUSED void " ++ releaseName ++ "(" ++ cType ++ " *value)"
              , "{"
              , "  if (value == NULL) return;"
              ]
              ++ releaseElements elementKind
              ++ [ "  *value = (" ++ cType ++ ") {NULL, 0};"
              , "}"
              , "#endif"
              , ""
              ]
         | True
         = error $ "SBV->C: Unsupported list element kind: " ++ show elementKind
       declaration kind = error $ "SBV->C: Expected a list kind, received " ++ show kind

       cloneElements elementKind
         | isExactGMPKind cfg elementKind
         =  [ "    for (size_t i = 0; i < value.length; ++i) {"
            , "      " ++ gmpOutputType elementKind ++ " element = (" ++ gmpOutputType elementKind ++ ") malloc(sizeof(*element));"
            , "      if (element == NULL) abort();"
            ]
         ++ map ("      " ++) (lines (render (gmpInitializeCopy elementKind (text "element") (text "value.data[i]"))))
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
         = [ "  " ++ listElementCType elementKind ++ " *data = (" ++ listElementCType elementKind ++ " *) value->data;"
           , "  for (size_t i = 0; i < value->length; ++i) {"
           , "    " ++ gmpOutputType elementKind ++ " element = (" ++ gmpOutputType elementKind ++ ") data[i];"
           , "    if (element != NULL) { " ++ gmpFunctionName elementKind "clear" ++ "(element); free(element); }"
           , "  }"
           , "  free(data);"
           ]
         | isConcreteADT elementKind || valueNeedsOwnership cfg elementKind
         = [ "  " ++ listElementCType elementKind ++ " *data = (" ++ listElementCType elementKind ++ " *) value->data;"
           , "  for (size_t i = 0; i < value->length; ++i)"
           , "    " ++ render (managedValueRelease elementKind (text "&data[i]"))
           , "  free(data);"
           ]
         | True
         = ["  free((void *) value->data);"]

-- | Emit forward declarations for list equality helpers referenced by nested
-- aggregate element comparisons.
listRuntimeDecls :: CgConfig -> [Kind] -> Doc
listRuntimeDecls cfg kinds = text . unlines $
  [ "static SBV_CGEN_UNUSED bool " ++ helperName kind "equal" ++ "(" ++ listCType kind ++ " left, " ++ listCType kind ++ " right);"
  | kind <- kinds
  , listSupported cfg kind
  ]

-- | Emit the shared list arena and specialized sequence operations for every
-- list kind used by the generated program.
listRuntime :: CgConfig -> Bool -> [Kind] -> Doc
listRuntime cfg usesExactInteger kinds = text . unlines . map markUnused $
     commonRuntime
  ++ (if usesExactInteger then exactIndexRuntime else [])
  ++ concatMap specializedRuntime kinds
 where markUnused line = case stripPrefix "static " line of
                           Just rest -> "static SBV_CGEN_UNUSED " ++ rest
                           Nothing   -> line

       specializedRuntime kind
         | listSupported cfg kind = listKindRuntime cfg usesExactInteger kind
         | True                   = error $ "SBV->C: Unsupported list kind: " ++ show kind

-- | Render a list constant with a caller-supplied renderer for its elements.
listConst :: (CV -> Doc) -> CV -> Maybe Doc
listConst renderElement (CV kind@(KList elementKind) (CList values))
  = Just $ text "((" P.<> text (listCType kind) P.<> text ") {"
       P.<> elements
       P.<> text ", "
       P.<> int (length values)
       P.<> text "})"
 where elements
         | null values = text "NULL"
         | True        = text "(" P.<> text (constElementCType elementKind) P.<> text "[]) {"
                      P.<> fsep (punctuate comma (map (arrayStoredValue elementKind . renderElement . CV elementKind) values))
                      P.<> text "}"
listConst _ _ = Nothing

-- | Lower the core symbolic sequence operations for non-character lists.
listExpr :: CgConfig -> Op -> [SV] -> SV -> [Doc] -> Maybe CLowering
listExpr cfg op svs resultSV args
  | not touchesList = Nothing
  | True            = case (op, args) of
      (ADTOp{}                   , _        )                    -> Nothing
      (TupleConstructor{}        , _        )                    -> Nothing
      (TupleAccess{}             , _        )                    -> Nothing
      (Uninterpreted{}           , _        )                    -> Nothing
      (Label _                   , [a]      )                    -> lower a
      (Equal _                   , [a, b]   )                    -> lower $ call (helper "equal") [a, b]
      (NotEqual                  , as       )                    -> lower $ distinctLists as
      (SeqOp (SeqLen kind)       , [a]      ) | kind /= KChar   -> lowerInteger False $ call (helperFor kind "length") [a]
      (SeqOp (SeqConcat _)       , as       )
        | KList elementKind <- resultKind                       -> lower $ foldLists elementKind as
      (SeqOp (SeqNth kind)       , [a, i]   ) | kind /= KChar   -> loadArray $ indexed kind "nth" [a] i
      (SeqOp (SeqUnit kind)      , [a]      ) | kind /= KChar   -> lower $ call (helperFor kind "unit") [text "&sbv_local_list_ctx", arrayStoredValue kind a]
      (SeqOp (SeqSubseq kind)    , [a, i, n]) | kind /= KChar   -> lower $ indexed2 kind "substring" a i n
      (SeqOp (SeqIndexOf kind)   , [a, b, i]) | kind /= KChar   -> lowerInteger True $ indexed kind "index_of" [a, b] i
      (SeqOp (SeqContains kind)  , [a, b]   ) | kind /= KChar   -> lower $ call (helperFor kind "contains") [a, b]
      (SeqOp (SeqPrefixOf kind)  , [a, b]   ) | kind /= KChar   -> lower $ call (helperFor kind "prefix_of") [a, b]
      (SeqOp (SeqSuffixOf kind)  , [a, b]   ) | kind /= KChar   -> lower $ call (helperFor kind "suffix_of") [a, b]
      (SeqOp (SeqReplace kind)   , [a, b, c]) | kind /= KChar   -> lower $ call (helperFor kind "replace") [text "&sbv_local_list_ctx", a, b, c]
      _ -> unsupported
 where resultKind = kindOf resultSV

       touchesList = isList resultKind || any (isList . kindOf) svs || isListOp op

       listKind = case [kind | value <- resultKind : map kindOf svs, kind@(KList _) <- [value]] of
                    kind:_ -> kind
                    []     -> error $ "SBV->C: Cannot determine list kind for " ++ show op

       lower expression = Just $ expressionLowering requirements expression

       loadArray expression
         | isArray resultKind = Just (arrayStoredLoad resultSV expression)
         | True               = lower expression

       lowerInteger signed expression
         | isExactGMPKind cfg resultKind
         = Just $ expressionLowering [CRequiresLists, CRequiresGMP]
                $ call (if signed then "sbv_gmp_integer_from_s64" else "sbv_gmp_integer_from_u64")
                       [text "&sbv_local_gmp_ctx", expression]
         | True
         = lower $ parens (text "SInteger") <+> expression

       requirements = CRequiresLists : [CRequiresGMP | any (isExactGMPKind cfg) touchedKinds]

       touchedKinds = concatMap expandKinds (resultKind : map kindOf svs)

       helper = helperName listKind

       helperFor elementKind = helperName (KList elementKind)

       distinctLists rendered = fsep $ punctuate (text " &&")
                                      [parens (text "!" P.<> call (helper "equal") [left, right])
                                      | (left:rest) <- tails rendered, right <- rest]

       foldLists _           []           = text "((" P.<> text (listCType listKind) P.<> text ") {NULL, 0})"
       foldLists _           [value]      = value
       foldLists elementKind (value:rest) = foldl combine value rest
         where combine left right = call (helperFor elementKind "concat") [text "&sbv_local_list_ctx", left, right]

       indexed elementKind suffix prefix index
        | exactIndex = call (helperFor elementKind (suffix ++ "_mpz")) (context ++ prefix ++ [index])
        | True       = call (helperFor elementKind suffix) (context ++ prefix ++ [parens (text "int64_t") <+> index])
        where context
                | suffix == "nth" && isExactGMPKind cfg elementKind = [text "&sbv_local_gmp_ctx"]
                | True                                               = []

       indexed2 elementKind suffix value offset count
         | exactIndex = call (helperFor elementKind (suffix ++ "_mpz")) [text "&sbv_local_list_ctx", value, offset, count]
         | True       = call (helperFor elementKind suffix)
                             [text "&sbv_local_list_ctx", value, parens (text "int64_t") <+> offset, parens (text "int64_t") <+> count]

       exactIndex = any (isExactGMPKind cfg . kindOf) svs

       requiresElementEquality Equal{}                 = True
       requiresElementEquality NotEqual                = True
       requiresElementEquality (SeqOp SeqIndexOf{})    = True
       requiresElementEquality (SeqOp SeqContains{})   = True
       requiresElementEquality (SeqOp SeqPrefixOf{})   = True
       requiresElementEquality (SeqOp SeqSuffixOf{})   = True
       requiresElementEquality (SeqOp SeqReplace{})    = True
       requiresElementEquality _                       = False

       unsupported
         | requiresElementEquality op
         , any isArray (expandKinds (listElementKind listKind))
         = error $ "SBV->C: List operation " ++ show op
                ++ " requires unsupported extensional equality for array-valued elements."
         | True
         = error $ "SBV->C: List lowering does not support " ++ show op
                ++ " with argument kinds " ++ show (map kindOf svs)
                ++ " and result kind " ++ show resultKind

-- | Compare two list descriptors using symbolic sequence equality.
listEqual :: Kind -> Doc -> Doc -> Doc
listEqual kind left right = call (helperName kind "equal") [left, right]

-- | Deep-copy a list across the generated function's ownership boundary.
listClone :: Kind -> Doc -> Doc
listClone kind value = call (listCloneName kind) [value]

-- | Release an owned list in a generated driver.
listRelease :: Kind -> Doc -> Doc
listRelease kind value = call (listReleaseName kind) [text "&" P.<> value] P.<> semi

-- | Produce a deterministic three-element list value for an example driver.
listDriverValue :: (Kind -> Integer -> Doc) -> Kind -> Integer -> Doc
listDriverValue renderValue kind@(KList elementKind) seed
  = text "((" P.<> text (listCType kind) P.<> text ") {"
       P.<> text "(" P.<> text (constElementCType elementKind) P.<> text "[]) {"
       P.<> fsep (punctuate comma [renderValue elementKind seed, renderValue elementKind (seed + 1), renderValue elementKind (seed + 2)])
       P.<> text "}, 3})"
listDriverValue _ kind _ = error $ "SBV->C: Expected a list kind, received " ++ show kind

-- | Initialize a generated-driver list whose elements require statement-based
-- setup. The descriptor borrows three independently initialized elements;
-- release their storage with 'listDriverClear' after the call completes. The
-- supplied statement renderer handles retained array and ADT elements.
listDriverInit :: CgConfig -> (Kind -> Integer -> Doc) -> (Kind -> String -> Integer -> Doc) -> Kind -> String -> Integer -> Doc
listDriverInit cfg renderValue initializeValue kind@KList{} externalName seed = valueDriverInit cfg renderValue initializeValue kind externalName seed
listDriverInit _   _           _               kind         _            _    = error $ "SBV->C: Expected a list kind, received " ++ show kind

-- | Clear managed element storage initialized by 'listDriverInit'.
listDriverClear :: CgConfig -> Kind -> String -> Doc
listDriverClear cfg kind@KList{} externalName = valueDriverClear cfg kind externalName
listDriverClear _   kind         _            = error $ "SBV->C: Expected a list kind, received " ++ show kind

-- | Print a list value using the supplied element printer.
listPrint :: (Kind -> Doc -> Doc) -> Kind -> Doc -> Doc
listPrint printElement (KList elementKind) value
  = text "printf(\"[\");"
 $$ text "for (size_t" <+> index <+> text "= 0;" <+> index <+> text "<" <+> value P.<> text ".length; ++" P.<> index P.<> text ")"
 $$ text "{"
 $$ nest 2 (   text "if" <+> parens (index <+> text "!= 0") <+> text "printf(\", \");"
            $$ printElement elementKind (value P.<> text ".data[" P.<> index P.<> text "]")
           )
 $$ text "}"
 $$ text "printf(\"]\");"
 where index = text ("sbv_local_list_print_index_" ++ kindTag elementKind)
listPrint _ kind _ = error $ "SBV->C: Expected a list kind, received " ++ show kind

-- | Initialize the arena used by list temporaries in a generated function.
listContextStart :: Doc
listContextStart = text "sbv_list_ctx sbv_local_list_ctx = {NULL};"

-- | Release all list temporaries allocated by a generated function.
listContextEnd :: Doc
listContextEnd = call "sbv_list_ctx_end" [text "&sbv_local_list_ctx"] P.<> semi

-- | Test whether an operation belongs to the non-character sequence family.
isListOp :: Op -> Bool
isListOp (SeqOp (SeqLen kind))      = kind /= KChar
isListOp (SeqOp (SeqConcat kind))   = kind /= KChar
isListOp (SeqOp (SeqNth kind))      = kind /= KChar
isListOp (SeqOp (SeqUnit kind))     = kind /= KChar
isListOp (SeqOp (SeqSubseq kind))   = kind /= KChar
isListOp (SeqOp (SeqIndexOf kind))  = kind /= KChar
isListOp (SeqOp (SeqContains kind)) = kind /= KChar
isListOp (SeqOp (SeqPrefixOf kind)) = kind /= KChar
isListOp (SeqOp (SeqSuffixOf kind)) = kind /= KChar
isListOp (SeqOp (SeqReplace kind))  = kind /= KChar
isListOp _                          = False

-- | Return the C type used to store one supported list element.
listElementCType :: Kind -> String
listElementCType KChar = "SChar"
listElementCType kind  = elementCType kind

-- | Return the preprocessor guard for one list forward declaration.
listForwardGuard :: Kind -> String
listForwardGuard kind = "SBV_LIST_" ++ kindTag (listElementKind kind) ++ "_FORWARD_DEFINED"

-- | Return the preprocessor guard for one list descriptor.
listGuard :: Kind -> String
listGuard kind = "SBV_LIST_" ++ kindTag (listElementKind kind) ++ "_DEFINED"

-- | Return the preprocessor guard for one list ownership-helper definition.
listOwnershipGuard :: Kind -> String
listOwnershipGuard kind = "SBV_LIST_" ++ kindTag (listElementKind kind) ++ "_OWNERSHIP_DEFINED"

-- | Return the element kind of a symbolic-list kind.
listElementKind :: Kind -> Kind
listElementKind (KList elementKind) = elementKind
listElementKind kind                = error $ "SBV->C: Expected a list kind, received " ++ show kind

-- | Return one specialized list-operation helper name.
helperName :: Kind -> String -> String
helperName = listHelperName

-- | Render a C helper call.
call :: String -> [Doc] -> Doc
call functionName args = text functionName P.<> parens (fsep (punctuate comma args))

-- | Shared per-call allocation arena used by every list specialization.
commonRuntime :: [String]
commonRuntime = arenaRuntime ListArena

-- | Exact-GMP index conversion shared by specialized list operations.
exactIndexRuntime :: [String]
exactIndexRuntime =
  ["static bool sbv_list_mpz_to_size(SInteger value, size_t *result)"
  , "{"
  , "  if (mpz_sgn(value) < 0 || mpz_sizeinbase(value, 2) > sizeof(size_t) * CHAR_BIT) return false;"
  , "  size_t written = 0; *result = 0;"
  , "  (void) mpz_export(result, &written, -1, sizeof(*result), 0, 0, value);"
  , "  return true;"
  , "}"
  ]

-- | Emit all sequence helpers for one supported list element kind.
listKindRuntime :: CgConfig -> Bool -> Kind -> [String]
listKindRuntime cfg usesExactInteger kind@(KList elementKind) =
  [ ""
  , "static bool " ++ equalElement ++ "(" ++ elementType ++ " left, " ++ elementType ++ " right)"
  , "{ return " ++ elementEqual ++ "; }"
  , "static bool " ++ equalList ++ "(" ++ listType ++ " left, " ++ listType ++ " right)"
  , "{"
  , "  if (left.length != right.length) return false;"
  , "  for (size_t i = 0; i < left.length; ++i) if (!" ++ equalElement ++ "(left.data[i], right.data[i])) return false;"
  , "  return true;"
  , "}"
  , "static uint64_t " ++ helper "length" ++ "(" ++ listType ++ " value) { return (uint64_t) value.length; }"
  , "static " ++ listType ++ " " ++ helper "concat" ++ "(sbv_list_ctx *ctx, " ++ listType ++ " left, " ++ listType ++ " right)"
  , "{"
  , "  if (right.length > SIZE_MAX - left.length) abort();"
  , "  if (left.length == 0) return right;"
  , "  if (right.length == 0) return left;"
  , "  const size_t length = left.length + right.length;"
  , "  " ++ elementType ++ " *data = (" ++ elementType ++ " *) sbv_list_alloc(ctx, length, sizeof(*data));"
  , "  if (left.length != 0) memcpy(data, left.data, left.length * sizeof(*data));"
  , "  if (right.length != 0) memcpy(data + left.length, right.data, right.length * sizeof(*data));"
  , "  return (" ++ listType ++ ") {data, length};"
  , "}"
  , "static " ++ listType ++ " " ++ helper "unit" ++ "(sbv_list_ctx *ctx, " ++ elementType ++ " value)"
  , "{"
  , "  " ++ elementType ++ " *data = (" ++ elementType ++ " *) sbv_list_alloc(ctx, 1, sizeof(*data));"
  , "  data[0] = value; return (" ++ listType ++ ") {data, 1};"
  , "}"
  , "static " ++ elementType ++ " " ++ helper "nth_size" ++ "(" ++ exactContextParam ++ listType ++ " value, size_t index)"
  , "{ return index < value.length ? value.data[index] : " ++ defaultElement ++ "; }"
  , "static " ++ elementType ++ " " ++ helper "nth" ++ "(" ++ exactContextParam ++ listType ++ " value, int64_t index)"
  , "{ return index < 0 ? " ++ defaultElement ++ " : " ++ helper "nth_size" ++ "(" ++ exactContextArg ++ "value, (size_t) index); }"
  , "static " ++ listType ++ " " ++ helper "substring_size" ++ "(sbv_list_ctx *ctx, " ++ listType ++ " value, size_t offset, size_t count)"
  , "{"
  , "  if (offset >= value.length || count == 0) return (" ++ listType ++ ") {NULL, 0};"
  , "  if (count > value.length - offset) count = value.length - offset;"
  , "  " ++ elementType ++ " *data = (" ++ elementType ++ " *) sbv_list_alloc(ctx, count, sizeof(*data));"
  , "  memcpy(data, value.data + offset, count * sizeof(*data)); return (" ++ listType ++ ") {data, count};"
  , "}"
  , "static " ++ listType ++ " " ++ helper "substring" ++ "(sbv_list_ctx *ctx, " ++ listType ++ " value, int64_t offset, int64_t count)"
  , "{"
  , "  if (offset < 0 || count <= 0) return (" ++ listType ++ ") {NULL, 0};"
  , "  return " ++ helper "substring_size" ++ "(ctx, value, (size_t) offset, (size_t) count);"
  , "}"
  ]
  ++ matchRuntime
  ++ [ "static bool " ++ helper "prefix_of" ++ "(" ++ listType ++ " prefix, " ++ listType ++ " value)"
     , "{ return prefix.length <= value.length && " ++ helper "match_at" ++ "(value, prefix, 0); }"
     , "static bool " ++ helper "suffix_of" ++ "(" ++ listType ++ " suffix, " ++ listType ++ " value)"
     , "{ return suffix.length <= value.length && " ++ helper "match_at" ++ "(value, suffix, value.length - suffix.length); }"
     , "static bool " ++ helper "contains" ++ "(" ++ listType ++ " value, " ++ listType ++ " part)"
     , "{ return " ++ helper "index_of_size" ++ "(value, part, 0) >= 0; }"
     , "static int64_t " ++ helper "index_of" ++ "(" ++ listType ++ " value, " ++ listType ++ " part, int64_t start)"
     , "{ return start < 0 ? -1 : " ++ helper "index_of_size" ++ "(value, part, (size_t) start); }"
     , "static " ++ listType ++ " " ++ helper "replace" ++ "(sbv_list_ctx *ctx, " ++ listType ++ " value, " ++ listType ++ " source, " ++ listType ++ " replacement)"
     , "{"
     , "  const int64_t index = " ++ helper "index_of_size" ++ "(value, source, 0);"
     , "  if (index < 0) return value;"
     , "  const size_t retained = value.length - source.length;"
     , "  if (replacement.length > SIZE_MAX - retained) abort();"
     , "  const size_t length = retained + replacement.length;"
     , "  " ++ elementType ++ " *data = (" ++ elementType ++ " *) sbv_list_alloc(ctx, length, sizeof(*data));"
     , "  const size_t first = (size_t) index; const size_t after = first + source.length;"
     , "  if (first != 0) memcpy(data, value.data, first * sizeof(*data));"
     , "  if (replacement.length != 0) memcpy(data + first, replacement.data, replacement.length * sizeof(*data));"
     , "  if (after != value.length) memcpy(data + first + replacement.length, value.data + after, (value.length - after) * sizeof(*data));"
     , "  return (" ++ listType ++ ") {data, length};"
     , "}"
     ]
  ++ exactRuntime
 where listType     = listCType kind
       elementType  = listElementCType elementKind
       helper       = helperName kind
       equalElement = helper "element_equal"
       equalList    = helper "equal"
       elementEqual = render $ byValueEqual cfg True elementKind (text "left") (text "right")

       exactContextParam
         | isExactGMPKind cfg elementKind = "sbv_gmp_ctx *exact_ctx, "
         | True                           = ""

       exactContextArg
         | isExactGMPKind cfg elementKind = "exact_ctx, "
         | True                           = ""

       defaultElement
         | isExactGMPKind cfg elementKind
         , elementKind == KUnbounded      = "sbv_gmp_integer_const(exact_ctx, \"0\")"
         | isExactGMPKind cfg elementKind = "sbv_gmp_real_const(exact_ctx, \"0\")"
         | True                           = "(" ++ elementType ++ ") {0}"

       matchRuntime =
         [ "static bool " ++ helper "match_at" ++ "(" ++ listType ++ " value, " ++ listType ++ " part, size_t offset)"
         , "{"
         , "  if (offset > value.length || part.length > value.length - offset) return false;"
         , "  for (size_t i = 0; i < part.length; ++i) if (!" ++ equalElement ++ "(value.data[offset + i], part.data[i])) return false;"
         , "  return true;"
         , "}"
         , "static int64_t " ++ helper "index_of_size" ++ "(" ++ listType ++ " value, " ++ listType ++ " part, size_t start)"
         , "{"
         , "  if (start > value.length) return -1;"
         , "  for (size_t i = start; i <= value.length; ++i) {"
         , "    if (" ++ helper "match_at" ++ "(value, part, i)) return i <= INT64_MAX ? (int64_t) i : -1;"
         , "    if (i == value.length) break;"
         , "  }"
         , "  return -1;"
         , "}"
         ]

       exactRuntime
         | usesExactInteger =
             [ "static " ++ elementType ++ " " ++ helper "nth_mpz" ++ "(" ++ exactContextParam ++ listType ++ " value, SInteger index)"
             , "{ size_t converted; return sbv_list_mpz_to_size(index, &converted) ? " ++ helper "nth_size" ++ "(" ++ exactContextArg ++ "value, converted) : " ++ defaultElement ++ "; }"
             , "static " ++ listType ++ " " ++ helper "substring_mpz" ++ "(sbv_list_ctx *ctx, " ++ listType ++ " value, SInteger offset, SInteger count)"
             , "{"
             , "  size_t converted_offset, converted_count;"
             , "  if (!sbv_list_mpz_to_size(offset, &converted_offset) || !sbv_list_mpz_to_size(count, &converted_count)) return (" ++ listType ++ ") {NULL, 0};"
             , "  return " ++ helper "substring_size" ++ "(ctx, value, converted_offset, converted_count);"
             , "}"
             , "static int64_t " ++ helper "index_of_mpz" ++ "(" ++ listType ++ " value, " ++ listType ++ " part, SInteger start)"
             , "{ size_t converted; return sbv_list_mpz_to_size(start, &converted) ? " ++ helper "index_of_size" ++ "(value, part, converted) : -1; }"
             ]
         | True = []
listKindRuntime _ _ kind = error $ "SBV->C: Expected a list kind, received " ++ show kind
