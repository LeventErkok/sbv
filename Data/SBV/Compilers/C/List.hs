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
  , listCType
  , listTypeDecls
  , listOwnershipTypeDecls
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

import Data.Char                       (toUpper)
import Data.List                       (nub, sortOn, stripPrefix, tails)
import qualified Data.Set as Set

import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as P ((<>))

import Data.SBV.Compilers.C.GMP        (gmpDriverClear, gmpDriverInit, isExactGMPKind)
import Data.SBV.Compilers.C.Lowering   (CLowering, CRequirement(..), CStorage(..), expressionLowering)
import Data.SBV.Compilers.C.Types      (elementCType, kindTag)
import Data.SBV.Compilers.C.Value      (byValueEqual, valueNeedsOwnership)
import Data.SBV.Compilers.CodeGen      (CgConfig)
import Data.SBV.Core.Data
import Data.SBV.Core.Kind              (expandKinds)

-- | Return all distinct symbolic-list kinds in dependency order.
listKinds :: Set.Set Kind -> [Kind]
listKinds = sortOn listDepth . nub . concatMap (filter isList . expandKinds) . Set.toAscList
 where listDepth :: Kind -> Int
       listDepth (KList elementKind) = 1 + listDepth elementKind
       listDepth _                   = 0

-- | Test whether a list element kind has a supported C representation.
listSupported :: CgConfig -> Kind -> Bool
listSupported cfg (KList elementKind) = supportedElement elementKind
 where supportedElement KBool          = True
       supportedElement KBounded{}     = True
       supportedElement KFloat         = True
       supportedElement KDouble        = True
       supportedElement KChar          = True
       supportedElement KFP{}          = True
       supportedElement KUnbounded     = True
       supportedElement KReal          = True
       supportedElement KRational      = True
       supportedElement (KTuple kinds) = all supportedTupleField kinds
       supportedElement kind           = isRoundingMode kind

       supportedTupleField tupleKind@(KTuple kinds) = not (valueNeedsOwnership cfg tupleKind)
                                                    && all supportedTupleField kinds
       supportedTupleField kind
         | valueNeedsOwnership cfg kind = False
         | True                         = supportedElement kind
listSupported _ _ = False

-- | Test whether a list stores exact GMP-backed elements.
listUsesExact :: CgConfig -> Kind -> Bool
listUsesExact cfg (KList elementKind) = isExactGMPKind cfg elementKind
listUsesExact _   _                   = False

-- | Return the public C descriptor type for a symbolic-list kind.
listCType :: Kind -> String
listCType kind@KList{} = elementCType kind
listCType kind         = error $ "SBV->C: Expected a list kind, received " ++ show kind

-- | Emit typed borrowed-list descriptors and ownership-helper prototypes.
-- The element type may remain incomplete here because descriptors only carry
-- pointers; definitions that inspect elements are emitted later by
-- 'listOwnershipTypeDecls'.
listTypeDecls :: CgConfig -> [Kind] -> Doc
listTypeDecls cfg kinds
  | null kinds = empty
  | True       = text . unlines $
      ["/* Typed symbolic lists. Inputs borrow their elements; outputs and returns own them. */"
      , "#ifndef SBV_CGEN_UNUSED"
      , "#if defined(__GNUC__) || defined(__clang__)"
      , "#define SBV_CGEN_UNUSED __attribute__((unused))"
      , "#else"
      , "#define SBV_CGEN_UNUSED"
      , "#endif"
      , "#endif"
      ]
      ++ concatMap declaration kinds
 where declaration kind@(KList elementKind)
         | listSupported cfg kind
         = let cType       = listCType kind
               elementType = listElementCType elementKind
               cloneName    = listCloneName kind
               releaseName  = listReleaseName kind
           in [ "#ifndef " ++ listGuard kind
              , "#define " ++ listGuard kind
              , "typedef struct { const " ++ elementType ++ " *data; size_t length; } " ++ cType ++ ";"
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
            , "      " ++ exactMutableType elementKind ++ " element = (" ++ exactMutableType elementKind ++ ") malloc(sizeof(*element));"
            , "      if (element == NULL) abort();"
            ]
         ++ exactInitialize elementKind
         ++ [ "      copy[i] = element;"
            , "    }"
            ]
         | True
         = ["    memcpy(copy, value.data, value.length * sizeof(*copy));"]

       releaseElements elementKind
         | isExactGMPKind cfg elementKind
         = [ "  " ++ listElementCType elementKind ++ " *data = (" ++ listElementCType elementKind ++ " *) value->data;"
           , "  for (size_t i = 0; i < value->length; ++i) {"
           , "    " ++ exactMutableType elementKind ++ " element = (" ++ exactMutableType elementKind ++ ") data[i];"
           , "    if (element != NULL) { " ++ exactClear elementKind ++ "(element); free(element); }"
           , "  }"
           , "  free(data);"
           ]
         | True
         = ["  free((void *) value->data);"]

       exactMutableType KUnbounded = "mpz_ptr"
       exactMutableType fieldKind
         | isExactGMPKind cfg fieldKind = "mpq_ptr"
       exactMutableType fieldKind       = error $ "SBV->C: Expected an exact list element, received " ++ show fieldKind

       exactInitialize KUnbounded = ["      mpz_init_set(element, value.data[i]);"]
       exactInitialize fieldKind
         | isExactGMPKind cfg fieldKind
         = [ "      mpq_init(element);"
           , "      mpq_set(element, value.data[i]);"
           ]
       exactInitialize fieldKind = error $ "SBV->C: Expected an exact list element, received " ++ show fieldKind

       exactClear KUnbounded = "mpz_clear"
       exactClear fieldKind
         | isExactGMPKind cfg fieldKind = "mpq_clear"
       exactClear fieldKind       = error $ "SBV->C: Expected an exact list element, received " ++ show fieldKind

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
         | True        = text "(const" <+> text (listElementCType elementKind) P.<> text "[]) {"
                      P.<> fsep (punctuate comma (map (renderElement . CV elementKind) values))
                      P.<> text "}"
listConst _ _ = Nothing

-- | Lower the core symbolic sequence operations for non-character lists.
listExpr :: CgConfig -> Op -> [SV] -> Kind -> [Doc] -> Maybe CLowering
listExpr cfg op svs resultKind args
  | not touchesList = Nothing
  | True            = case (op, args) of
      (ADTOp{}                   , _        )                    -> Nothing
      (TupleConstructor{}        , _        )                    -> Nothing
      (TupleAccess{}             , _        )                    -> Nothing
      (Label _                   , [a]      )                    -> lower a
      (Ite                       , [c, a, b])                    -> lower $ c <+> text "?" <+> a <+> text ":" <+> b
      (Equal _                   , [a, b]   )                    -> lower $ call (helper "equal") [a, b]
      (NotEqual                  , as       )                    -> lower $ distinctLists as
      (SeqOp (SeqLen kind)       , [a]      ) | kind /= KChar   -> lowerInteger False $ call (helperFor kind "length") [a]
      (SeqOp (SeqConcat kind)    , as       ) | kind /= KChar   -> lower $ foldLists kind as
      (SeqOp (SeqNth kind)       , [a, i]   ) | kind /= KChar   -> lower $ indexed kind "nth" [a] i
      (SeqOp (SeqUnit kind)      , [a]      ) | kind /= KChar   -> lower $ call (helperFor kind "unit") [text "&__sbv_list_ctx", a]
      (SeqOp (SeqSubseq kind)    , [a, i, n]) | kind /= KChar   -> lower $ indexed2 kind "substring" a i n
      (SeqOp (SeqIndexOf kind)   , [a, b, i]) | kind /= KChar   -> lowerInteger True $ indexed kind "index_of" [a, b] i
      (SeqOp (SeqContains kind)  , [a, b]   ) | kind /= KChar   -> lower $ call (helperFor kind "contains") [a, b]
      (SeqOp (SeqPrefixOf kind)  , [a, b]   ) | kind /= KChar   -> lower $ call (helperFor kind "prefix_of") [a, b]
      (SeqOp (SeqSuffixOf kind)  , [a, b]   ) | kind /= KChar   -> lower $ call (helperFor kind "suffix_of") [a, b]
      (SeqOp (SeqReplace kind)   , [a, b, c]) | kind /= KChar   -> lower $ call (helperFor kind "replace") [text "&__sbv_list_ctx", a, b, c]
      _ -> unsupported
 where touchesList = isList resultKind || any (isList . kindOf) svs || isListOp op

       listKind = case [kind | value <- resultKind : map kindOf svs, kind@(KList _) <- [value]] of
                    kind:_ -> kind
                    []     -> error $ "SBV->C: Cannot determine list kind for " ++ show op

       lower expression = Just $ expressionLowering storage requirements expression

       lowerInteger signed expression
         | isExactGMPKind cfg resultKind
         = Just $ expressionLowering CFunctionScoped [CRequiresLists, CRequiresGMP]
                $ call (if signed then "sbv_gmp_integer_from_s64" else "sbv_gmp_integer_from_u64")
                       [text "&__sbv_gmp_ctx", expression]
         | True
         = lower $ parens (text "SInteger") <+> expression

       storage
         | isList resultKind             = CFunctionScoped
         | isExactGMPKind cfg resultKind = CFunctionScoped
         | True                          = CByValue

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
         where combine left right = call (helperFor elementKind "concat") [text "&__sbv_list_ctx", left, right]

       indexed elementKind suffix prefix index
        | exactIndex = call (helperFor elementKind (suffix ++ "_mpz")) (context ++ prefix ++ [index])
        | True       = call (helperFor elementKind suffix) (context ++ prefix ++ [parens (text "int64_t") <+> index])
        where context
                | suffix == "nth" && isExactGMPKind cfg elementKind = [text "&__sbv_gmp_ctx"]
                | True                                               = []

       indexed2 elementKind suffix value offset count
         | exactIndex = call (helperFor elementKind (suffix ++ "_mpz")) [text "&__sbv_list_ctx", value, offset, count]
         | True       = call (helperFor elementKind suffix)
                             [text "&__sbv_list_ctx", value, parens (text "int64_t") <+> offset, parens (text "int64_t") <+> count]

       exactIndex = any (isExactGMPKind cfg . kindOf) svs

       unsupported = error $ "SBV->C: List lowering does not support " ++ show op
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
       P.<> text "(const" <+> text (listElementCType elementKind) P.<> text "[]) {"
       P.<> fsep (punctuate comma [renderValue elementKind seed, renderValue elementKind (seed + 1), renderValue elementKind (seed + 2)])
       P.<> text "}, 3})"
listDriverValue _ kind _ = error $ "SBV->C: Expected a list kind, received " ++ show kind

-- | Initialize a generated-driver list whose elements use exact GMP storage.
-- The resulting descriptor borrows three independently initialized elements;
-- release them with 'listDriverClear' after the generated call completes.
listDriverInit :: CgConfig -> Kind -> String -> Integer -> Doc
listDriverInit cfg kind@(KList elementKind) externalName seed
  | isExactGMPKind cfg elementKind
  = vcat (zipWith initializeElement elementNames [seed ..])
 $$ text "const" <+> text (listElementCType elementKind) <+> text dataName P.<> brackets (int elementCount)
      <+> text "=" <+> braces (fsep (punctuate comma (map text elementNames))) P.<> semi
 $$ text "const" <+> text (listCType kind) <+> text externalName <+> text "="
      <+> braces (fsep (punctuate comma [text dataName, int elementCount])) P.<> semi
 where elementCount = 3
       elementNames = [externalName ++ "_element_" ++ show index | index <- [0 :: Int .. elementCount - 1]]
       dataName     = externalName ++ "_data"

       initializeElement elementName value = gmpDriverInit elementKind (text elementName) (integer value)
listDriverInit _ kind _ _ = error $ "SBV->C: Expected an exact-element list kind, received " ++ show kind

-- | Clear the exact GMP elements initialized by 'listDriverInit'.
listDriverClear :: CgConfig -> Kind -> String -> Doc
listDriverClear cfg (KList elementKind) externalName
  | isExactGMPKind cfg elementKind
  = vcat [gmpDriverClear elementKind (text (externalName ++ "_element_" ++ show index)) | index <- [0 :: Int .. 2]]
listDriverClear _ kind _ = error $ "SBV->C: Expected an exact-element list kind, received " ++ show kind

-- | Print a list value using the supplied element printer.
listPrint :: (Kind -> Doc -> Doc) -> Kind -> Doc -> Doc
listPrint printElement (KList elementKind) value
  = text "printf(\"[\");"
 $$ text "for (size_t __sbv_list_print_index = 0; __sbv_list_print_index <" <+> value P.<> text ".length; ++__sbv_list_print_index)"
 $$ text "{"
 $$ nest 2 (   text "if (__sbv_list_print_index != 0) printf(\", \");"
            $$ printElement elementKind (value P.<> text ".data[__sbv_list_print_index]")
           )
 $$ text "}"
 $$ text "printf(\"]\");"
listPrint _ kind _ = error $ "SBV->C: Expected a list kind, received " ++ show kind

-- | Initialize the arena used by list temporaries in a generated function.
listContextStart :: Doc
listContextStart = text "sbv_list_ctx __sbv_list_ctx = {NULL};"

-- | Release all list temporaries allocated by a generated function.
listContextEnd :: Doc
listContextEnd = call "sbv_list_ctx_end" [text "&__sbv_list_ctx"] P.<> semi

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

-- | Return the collision-free suffix used by a list descriptor and helpers.
listKindTag :: Kind -> String
listKindTag KChar = "char"
listKindTag kind  = kindTag kind

-- | Return the preprocessor guard for one list descriptor.
listGuard :: Kind -> String
listGuard kind = "SBV_LIST_" ++ map toUpper (listKindTag (listElementKind kind)) ++ "_DEFINED"

-- | Return the preprocessor guard for one list ownership-helper definition.
listOwnershipGuard :: Kind -> String
listOwnershipGuard kind = "SBV_LIST_" ++ map toUpper (listKindTag (listElementKind kind)) ++ "_OWNERSHIP_DEFINED"

-- | Return the element kind of a symbolic-list kind.
listElementKind :: Kind -> Kind
listElementKind (KList elementKind) = elementKind
listElementKind kind                = error $ "SBV->C: Expected a list kind, received " ++ show kind

-- | Return the generated clone-helper name for a list kind.
listCloneName :: Kind -> String
listCloneName kind = "sbv_list_clone_" ++ listKindTag (listElementKind kind)

-- | Return the generated release-helper name for a list kind.
listReleaseName :: Kind -> String
listReleaseName kind = "sbv_list_release_" ++ listKindTag (listElementKind kind)

-- | Return one specialized list-operation helper name.
helperName :: Kind -> String -> String
helperName kind suffix = "sbv_list_" ++ listKindTag (listElementKind kind) ++ "_" ++ suffix

-- | Render a C helper call.
call :: String -> [Doc] -> Doc
call functionName args = text functionName P.<> parens (fsep (punctuate comma args))

-- | Shared per-call allocation arena used by every list specialization.
commonRuntime :: [String]
commonRuntime =
  ["/* Per-call ownership arena for symbolic-list temporaries. */"
  , "typedef struct sbv_list_node { struct sbv_list_node *next; long double data[]; } sbv_list_node;"
  , "typedef struct { sbv_list_node *head; } sbv_list_ctx;"
  , "static void *sbv_list_alloc(sbv_list_ctx *ctx, size_t count, size_t element_size)"
  , "{"
  , "  if (count == 0) return NULL;"
  , "  if (element_size == 0 || count > SIZE_MAX / element_size) abort();"
  , "  const size_t bytes = count * element_size;"
  , "  if (bytes > SIZE_MAX - sizeof(sbv_list_node)) abort();"
  , "  sbv_list_node *node = (sbv_list_node *) malloc(sizeof(*node) + bytes);"
  , "  if (node == NULL) abort();"
  , "  node->next = ctx->head; ctx->head = node; return node->data;"
  , "}"
  , "static void sbv_list_ctx_end(sbv_list_ctx *ctx)"
  , "{"
  , "  while (ctx->head != NULL) {"
  , "    sbv_list_node *next = ctx->head->next; free(ctx->head); ctx->head = next;"
  , "  }"
  , "}"
  ]

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
