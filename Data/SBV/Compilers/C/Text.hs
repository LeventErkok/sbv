-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.Text
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Length-aware character and string lowering for generated C.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.Text
  ( textTypeDecls
  , textRuntime
  , textConst
  , textExpr
  , textPrint
  , textClone
  , textRelease
  , textDriverValue
  , textContextStart
  , textContextEnd
  ) where

import Data.Bits                       ((.&.), (.|.), shiftR)
import Data.Char                       (chr, ord)
import Data.List                       (intercalate, stripPrefix, tails)
import qualified Data.Set as Set
import Numeric                         (showHex)

import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as P ((<>))

import Data.SBV.Compilers.C.GMP        (isExactGMPKind)
import Data.SBV.Compilers.C.Lowering   (CLowering, CRequirement(..), CStorage(..), expressionLowering)
import Data.SBV.Compilers.CodeGen      (CgConfig)
import Data.SBV.Core.Data

-- | Declare the public character and string C types. String inputs borrow
-- their bytes for the duration of a generated call; returned and output
-- strings own their bytes and must be released with @sbv_string_release@.
textTypeDecls :: Set.Set Kind -> Doc
textTypeDecls kinds
  | not usesText = empty
  | True         = text . unlines $
      ["/* Characters and length-aware UTF-8-compatible strings. */"
      , "/* SString inputs borrow their bytes for the duration of a generated call. */"
      , "/* SString outputs and returns own their bytes; release them with sbv_string_release. */"
      , "/* sbv_string_borrow preserves embedded NULs; sbv_string_borrow_utf8 is for NUL-terminated input. */"
      , "/* Borrowed text must use the canonical encoding below and character codes must be at most 0x2ffff. */"
      , "#ifndef SBV_TEXT_TYPES_DEFINED"
      , "#define SBV_TEXT_TYPES_DEFINED"
      , "#include <limits.h>"
      , "#ifndef SBV_CGEN_UNUSED"
      , "#if defined(__GNUC__) || defined(__clang__)"
      , "#define SBV_CGEN_UNUSED __attribute__((unused))"
      , "#else"
      , "#define SBV_CGEN_UNUSED"
      , "#endif"
      , "#endif"
      , "typedef uint32_t SChar;"
      , "typedef struct {"
      , "  const uint8_t *data;"
      , "  size_t byte_length;"
      , "  size_t length;"
      , "} SString;"
      , ""
      , "static inline SString sbv_string_borrow(const uint8_t *data, size_t byte_length, size_t length)"
      , "{"
      , "  const SString result = {data, byte_length, length};"
      , "  return result;"
      , "}"
      , ""
      , "static inline SString sbv_string_borrow_utf8(const char *value)"
      , "{"
      , "  const size_t byte_length = value == NULL ? 0 : strlen(value);"
      , "  size_t length = 0;"
      , "  for (size_t i = 0; i < byte_length; ++i)"
      , "    if ((((const uint8_t *) value)[i] & UINT8_C(0xc0)) != UINT8_C(0x80)) ++length;"
      , "  return sbv_string_borrow((const uint8_t *) value, byte_length, length);"
      , "}"
      , ""
      , "static inline SString sbv_string_clone(SString value)"
      , "{"
      , "  uint8_t *copy = NULL;"
      , "  if (value.byte_length != 0) {"
      , "    copy = (uint8_t *) malloc(value.byte_length);"
      , "    if (copy == NULL) abort();"
      , "    memcpy(copy, value.data, value.byte_length);"
      , "  }"
      , "  return sbv_string_borrow(copy, value.byte_length, value.length);"
      , "}"
      , ""
      , "static inline void sbv_string_release(SString *value)"
      , "{"
      , "  if (value == NULL) return;"
      , "  free((void *) value->data);"
      , "  *value = sbv_string_borrow(NULL, 0, 0);"
      , "}"
      , ""
      , "static inline void sbv_string_fprint(FILE *stream, SString value)"
      , "{"
      , "  if (value.byte_length != 0) (void) fwrite(value.data, 1, value.byte_length, stream);"
      , "}"
      , ""
      , "static inline size_t sbv_char_encode(SChar value, uint8_t bytes[4])"
      , "{"
      , "  if (value > UINT32_C(0x2ffff)) abort();"
      , "  if (value <= UINT32_C(0x7f)) { bytes[0] = (uint8_t) value; return 1; }"
      , "  if (value <= UINT32_C(0x7ff)) {"
      , "    bytes[0] = (uint8_t) (UINT32_C(0xc0) | (value >> 6));"
      , "    bytes[1] = (uint8_t) (UINT32_C(0x80) | (value & UINT32_C(0x3f)));"
      , "    return 2;"
      , "  }"
      , "  if (value <= UINT32_C(0xffff)) {"
      , "    bytes[0] = (uint8_t) (UINT32_C(0xe0) | (value >> 12));"
      , "    bytes[1] = (uint8_t) (UINT32_C(0x80) | ((value >> 6) & UINT32_C(0x3f)));"
      , "    bytes[2] = (uint8_t) (UINT32_C(0x80) | (value & UINT32_C(0x3f)));"
      , "    return 3;"
      , "  }"
      , "  bytes[0] = (uint8_t) (UINT32_C(0xf0) | (value >> 18));"
      , "  bytes[1] = (uint8_t) (UINT32_C(0x80) | ((value >> 12) & UINT32_C(0x3f)));"
      , "  bytes[2] = (uint8_t) (UINT32_C(0x80) | ((value >> 6) & UINT32_C(0x3f)));"
      , "  bytes[3] = (uint8_t) (UINT32_C(0x80) | (value & UINT32_C(0x3f)));"
      , "  return 4;"
      , "}"
      , ""
      , "static inline void sbv_char_fprint(FILE *stream, SChar value)"
      , "{"
      , "  uint8_t bytes[4];"
      , "  const size_t count = sbv_char_encode(value, bytes);"
      , "  (void) fwrite(bytes, 1, count, stream);"
      , "}"
      , "#endif"
      , ""
      ]
 where usesText = KString `Set.member` kinds || KChar `Set.member` kinds

-- | Emit the per-call text arena and the helpers used by string operations.
textRuntime :: CgConfig -> Bool -> Doc
textRuntime cfg usesExactInteger = text . unlines . map markUnused $
     commonRuntime
  ++ nativeIntegerRuntime
  ++ if usesExactInteger then exactIntegerRuntime else []
 where markUnused line = case stripPrefix "static " line of
                           Just rest -> "static SBV_CGEN_UNUSED " ++ rest
                           Nothing   -> line

       nativeIntegerRuntime
         | isExactGMPKind cfg KUnbounded = []
         | True                          = nativeIntegerHelpers

-- | Render a character or string constant without relying on C string
-- escaping, so embedded NULs and arbitrary character codes are preserved.
textConst :: CV -> Maybe Doc
textConst (CV KChar (CChar value))
  | ord value > 0x2ffff = error $ "SBV->C: Character literal exceeds the SMT-LIB maximum: " ++ show value
  | True                = Just $ text (charLiteral value)
textConst (CV KString (CString value))
  | any ((> 0x2ffff) . ord) value = error "SBV->C: String literal contains a character exceeding the SMT-LIB maximum"
  | True                          = Just $ text "((SString) {"
       P.<> dataBytes
       P.<> text ", "
       P.<> integer (fromIntegral (length bytes))
       P.<> text ", "
       P.<> integer (fromIntegral (length value))
       P.<> text "})"
 where bytes = concatMap encodeChar value
       dataBytes
         | null bytes = text "NULL"
         | True       = text "(const uint8_t[]) {" P.<> text (intercalate ", " (map byteLiteral bytes)) P.<> text "}"
textConst _ = Nothing

-- | Lower character and string operations. Sequence operations are accepted
-- here only when their element kind is 'KChar'; general sequences are handled
-- by the list runtime.
textExpr :: CgConfig -> Op -> [SV] -> Kind -> [Doc] -> Maybe CLowering
textExpr cfg op svs resultKind args
  | not touchesText = Nothing
  | True            = case (op, args) of
      (ADTOp{}                   , _        ) -> Nothing
      (Uninterpreted{}           , _        ) -> Nothing
      (Label _                   , [a]      ) -> lower a
      (Ite                       , [c, a, b]) -> lower $ c <+> text "?" <+> a <+> text ":" <+> b
      (Equal _                   , [a, b]   ) -> lower $ equal a b
      (NotEqual                  , as       ) -> lower $ distinctText as
      (LessThan                  , [a, b]   ) -> lower $ ordered "<"  a b
      (GreaterThan               , [a, b]   ) -> lower $ ordered ">"  a b
      (LessEq                    , [a, b]   ) -> lower $ ordered "<=" a b
      (GreaterEq                 , [a, b]   ) -> lower $ ordered ">=" a b
      (SeqOp (SeqLen KChar)      , [a]      ) -> lowerInteger False $ text "sbv_text_length" P.<> parens a
      (SeqOp (SeqConcat KChar)   , as       ) -> lower $ foldText "sbv_text_concat" as
      (SeqOp (SeqNth KChar)      , [a, i]   ) -> lower $ indexed "sbv_text_nth" [a] i
      (SeqOp (SeqUnit KChar)     , [a]      ) -> lower $ call "sbv_text_unit" [text "&__sbv_text_ctx", a]
      (SeqOp (SeqSubseq KChar)   , [a, i, n]) -> lower $ indexed2 "sbv_text_substring" a i n
      (SeqOp (SeqIndexOf KChar)  , [a, b, i]) -> lowerInteger True $ indexed "sbv_text_index_of" [a, b] i
      (SeqOp (SeqContains KChar) , [a, b]   ) -> lower $ call "sbv_text_contains" [a, b]
      (SeqOp (SeqPrefixOf KChar) , [a, b]   ) -> lower $ call "sbv_text_prefix_of" [a, b]
      (SeqOp (SeqSuffixOf KChar) , [a, b]   ) -> lower $ call "sbv_text_suffix_of" [a, b]
      (SeqOp (SeqReplace KChar)  , [a, b, c]) -> lower $ call "sbv_text_replace" [text "&__sbv_text_ctx", a, b, c]
      (StrOp StrToCode           , [a]      ) -> lowerInteger False a
      (StrOp StrFromCode         , [a]      ) -> lower $ fromCode a
      (StrOp StrStrToNat         , [a]      ) -> lowerNat a
      (StrOp StrNatToStr         , [a]      ) -> lower $ fromNat a
      (StrOp StrInRe{}           , _        ) -> solverOnly "regular-expression membership"
      (TupleConstructor{}        , _        ) -> Nothing
      (TupleAccess{}             , _        ) -> Nothing
      _                                         -> unsupported (show op)
 where touchesText = resultKind `elem` [KChar, KString]
                  || any ((`elem` [KChar, KString]) . kindOf) svs
                  || isTextOp op

       lower expression = Just $ expressionLowering storage [CRequiresText] expression

       lowerNat value
         | isExactGMPKind cfg resultKind
         = Just $ expressionLowering CFunctionScoped [CRequiresText, CRequiresGMP] (toNat value)
         | True
         = lower $ parens (text "SInteger") <+> toNat value

       lowerInteger signed expression
         | isExactGMPKind cfg resultKind
         = Just $ expressionLowering CFunctionScoped [CRequiresText, CRequiresGMP]
                $ call (if signed then "sbv_gmp_integer_from_s64" else "sbv_gmp_integer_from_u64")
                       [text "&__sbv_gmp_ctx", expression]
         | True
         = lower $ parens (text "SInteger") <+> expression

       storage
         | resultKind == KString = CFunctionScoped
         | True                  = CByValue

       usesString = any ((== KString) . kindOf) svs

       equal a b
         | usesString = parens $ call "sbv_text_compare" [a, b] <+> text "== 0"
         | True       = a <+> text "==" <+> b

       ordered relation a b
         | usesString = parens $ call "sbv_text_compare" [a, b] <+> text relation <+> text "0"
         | True       = a <+> text relation <+> b

       distinctText as = fsep $ punctuate (text " &&")
                              [parens (if usesString
                                       then call "sbv_text_compare" [a, b] <+> text "!= 0"
                                       else a <+> text "!=" <+> b)
                              | (a:rest) <- tails as, b <- rest]

       foldText _      []     = text "((SString) {NULL, 0, 0})"
       foldText _      [a]    = a
       foldText helper (a:as) = foldl (\left right -> call helper [text "&__sbv_text_ctx", left, right]) a as

       indexed helper prefix index
         | exactIndex = call (helper ++ "_mpz") (prefix ++ [index])
         | True       = call helper (prefix ++ [parens (text "int64_t") <+> index])

       indexed2 helper value offset count
         | exactIndex = call (helper ++ "_mpz") [text "&__sbv_text_ctx", value, offset, count]
         | True       = call helper [text "&__sbv_text_ctx", value, parens (text "int64_t") <+> offset, parens (text "int64_t") <+> count]

       exactIndex = any (isExactGMPKind cfg . kindOf) svs

       fromCode value
         | exactIndex = call "sbv_text_from_code_mpz" [value]
         | True       = call "sbv_text_from_code" [parens (text "int64_t") <+> value]

       toNat value
         | isExactGMPKind cfg resultKind
         = call "sbv_text_to_nat_mpz" [text "&__sbv_gmp_ctx", text "&__sbv_text_ctx", value]
         | True
         = call "sbv_text_to_nat" [value]

       fromNat value
         | exactIndex = call "sbv_text_from_nat_mpz" [text "&__sbv_text_ctx", value]
         | True       = call "sbv_text_from_nat" [text "&__sbv_text_ctx", parens (text "int64_t") <+> value]

       unsupported what = error $ "SBV->C: text lowering does not yet support " ++ what
                               ++ " with argument kinds " ++ show (map kindOf svs)
                               ++ " and result kind " ++ show resultKind

       solverOnly feature = error $ "SBV->C: " ++ feature ++ " has solver-only semantics and cannot be compiled to executable C"

-- | Print a generated character or string value to standard output.
textPrint :: Kind -> Doc -> Doc
textPrint KChar   value = call "sbv_char_fprint"   [text "stdout", value]
textPrint KString value = call "sbv_string_fprint" [text "stdout", value]
textPrint kind    _     = error $ "SBV->C: Expected a text kind, received " ++ show kind

-- | Deep-copy a string across the generated function's ownership boundary.
textClone :: Doc -> Doc
textClone value = call "sbv_string_clone" [value]

-- | Release an owned string in a generated driver.
textRelease :: Doc -> Doc
textRelease value = call "sbv_string_release" [text "&" P.<> value] P.<> semi

-- | Produce a deterministic printable driver value for a character or string.
textDriverValue :: Kind -> Integer -> Doc
textDriverValue KChar   seed = text $ charLiteral $ chr $ 32 + fromInteger (abs seed `mod` 95)
textDriverValue KString seed = case textConst (CV KString (CString ("sbv" ++ show (abs seed `mod` 1000)))) of
                                Just value -> value
                                Nothing    -> error "SBV->C: Impossible string driver value"
textDriverValue kind    _    = error $ "SBV->C: Expected a text kind, received " ++ show kind

-- | Initialize the arena used by string temporaries in a generated function.
textContextStart :: Doc
textContextStart = text "sbv_text_ctx __sbv_text_ctx = {NULL};"

-- | Release all string temporaries allocated by a generated function.
textContextEnd :: Doc
textContextEnd = call "sbv_text_ctx_end" [text "&__sbv_text_ctx"] P.<> semi

-- | Test whether an operation belongs to the string/character family even
-- when neither its result nor all of its operands have a text kind.
isTextOp :: Op -> Bool
isTextOp StrOp{}                        = True
isTextOp (SeqOp (SeqLen KChar))         = True
isTextOp (SeqOp (SeqConcat KChar))      = True
isTextOp (SeqOp (SeqNth KChar))         = True
isTextOp (SeqOp (SeqUnit KChar))        = True
isTextOp (SeqOp (SeqSubseq KChar))      = True
isTextOp (SeqOp (SeqIndexOf KChar))     = True
isTextOp (SeqOp (SeqContains KChar))    = True
isTextOp (SeqOp (SeqPrefixOf KChar))    = True
isTextOp (SeqOp (SeqSuffixOf KChar))    = True
isTextOp (SeqOp (SeqReplace KChar))     = True
isTextOp _                              = False

-- | Render a portable numeric C character literal.
charLiteral :: Char -> String
charLiteral value = "UINT32_C(0x" ++ replicate (8 - length rendered) '0' ++ rendered ++ ")"
 where rendered = showHex (ord value) ""

-- | Encode one Haskell character with the canonical one-to-four-byte scheme
-- used by the generated runtime. Numeric surrogate values are preserved.
encodeChar :: Char -> [Int]
encodeChar value
  | code <= 0x7f   = [code]
  | code <= 0x7ff  = [0xc0 .|. (code `shiftR` 6), 0x80 .|. (code .&. 0x3f)]
  | code <= 0xffff = [ 0xe0 .|. (code `shiftR` 12)
                      , 0x80 .|. ((code `shiftR` 6) .&. 0x3f)
                      , 0x80 .|. (code .&. 0x3f)
                      ]
  | True           = [ 0xf0 .|. (code `shiftR` 18)
                      , 0x80 .|. ((code `shiftR` 12) .&. 0x3f)
                      , 0x80 .|. ((code `shiftR` 6) .&. 0x3f)
                      , 0x80 .|. (code .&. 0x3f)
                      ]
 where code = ord value

-- | Render one encoded byte as a fixed-width portable C literal.
byteLiteral :: Int -> String
byteLiteral value = "UINT8_C(0x" ++ replicate (2 - length rendered) '0' ++ rendered ++ ")"
 where rendered = showHex value ""

-- | Render a C helper call.
call :: String -> [Doc] -> Doc
call functionName args = text functionName P.<> parens (fsep (punctuate comma args))

-- | Runtime helpers shared by mapped and exact integer configurations.
commonRuntime :: [String]
commonRuntime =
  ["/* Per-call ownership arena for string temporaries. */"
  , "typedef struct sbv_text_node { struct sbv_text_node *next; uint8_t data[]; } sbv_text_node;"
  , "typedef struct { sbv_text_node *head; } sbv_text_ctx;"
  , ""
  , "static uint8_t *sbv_text_alloc(sbv_text_ctx *ctx, size_t count)"
  , "{"
  , "  if (count == 0) return NULL;"
  , "  sbv_text_node *node = (sbv_text_node *) malloc(sizeof(*node) + count);"
  , "  if (node == NULL) abort();"
  , "  node->next = ctx->head; ctx->head = node; return node->data;"
  , "}"
  , ""
  , "static void sbv_text_ctx_end(sbv_text_ctx *ctx)"
  , "{"
  , "  while (ctx->head != NULL) {"
  , "    sbv_text_node *next = ctx->head->next; free(ctx->head); ctx->head = next;"
  , "  }"
  , "}"
  , ""
  , "static size_t sbv_text_width(uint8_t first)"
  , "{"
  , "  if (first < UINT8_C(0x80)) return 1;"
  , "  if (first < UINT8_C(0xe0)) return 2;"
  , "  if (first < UINT8_C(0xf0)) return 3;"
  , "  return 4;"
  , "}"
  , ""
  , "static size_t sbv_text_byte_offset(SString value, size_t index)"
  , "{"
  , "  size_t byte = 0;"
  , "  for (size_t character = 0; character < index && byte < value.byte_length; ++character)"
  , "    byte += sbv_text_width(value.data[byte]);"
  , "  return byte;"
  , "}"
  , ""
  , "static SChar sbv_text_decode(const uint8_t *bytes)"
  , "{"
  , "  const size_t width = sbv_text_width(bytes[0]);"
  , "  if (width == 1) return bytes[0];"
  , "  SChar result = bytes[0] & (width == 2 ? UINT8_C(0x1f) : width == 3 ? UINT8_C(0x0f) : UINT8_C(0x07));"
  , "  for (size_t i = 1; i < width; ++i) result = (result << 6) | (bytes[i] & UINT8_C(0x3f));"
  , "  return result;"
  , "}"
  , ""
  , "static uint64_t sbv_text_length(SString value) { return (uint64_t) value.length; }"
  , ""
  , "static int sbv_text_compare(SString left, SString right)"
  , "{"
  , "  const size_t common = left.byte_length < right.byte_length ? left.byte_length : right.byte_length;"
  , "  const int prefix = common == 0 ? 0 : memcmp(left.data, right.data, common);"
  , "  if (prefix != 0) return prefix;"
  , "  return left.byte_length < right.byte_length ? -1 : left.byte_length > right.byte_length ? 1 : 0;"
  , "}"
  , ""
  , "static SString sbv_text_concat(sbv_text_ctx *ctx, SString left, SString right)"
  , "{"
  , "  if (SIZE_MAX - left.byte_length < right.byte_length || SIZE_MAX - left.length < right.length) abort();"
  , "  const size_t byte_length = left.byte_length + right.byte_length;"
  , "  uint8_t *data = sbv_text_alloc(ctx, byte_length);"
  , "  if (left.byte_length != 0) memcpy(data, left.data, left.byte_length);"
  , "  if (right.byte_length != 0) memcpy(data + left.byte_length, right.data, right.byte_length);"
  , "  return sbv_string_borrow(data, byte_length, left.length + right.length);"
  , "}"
  , ""
  , "static SString sbv_text_unit(sbv_text_ctx *ctx, SChar value)"
  , "{"
  , "  uint8_t encoded[4];"
  , "  const size_t count = sbv_char_encode(value, encoded);"
  , "  uint8_t *data = sbv_text_alloc(ctx, count); memcpy(data, encoded, count);"
  , "  return sbv_string_borrow(data, count, 1);"
  , "}"
  , ""
  , "static SChar sbv_text_nth(SString value, int64_t index)"
  , "{"
  , "  if (index < 0 || (uint64_t) index >= value.length) return UINT32_C(0);"
  , "  return sbv_text_decode(value.data + sbv_text_byte_offset(value, (size_t) index));"
  , "}"
  , ""
  , "static SString sbv_text_substring_size(sbv_text_ctx *ctx, SString value, size_t offset, size_t count)"
  , "{"
  , "  if (offset >= value.length || count == 0) return sbv_string_borrow(NULL, 0, 0);"
  , "  if (count > value.length - offset) count = value.length - offset;"
  , "  const size_t first = sbv_text_byte_offset(value, offset);"
  , "  const size_t last = sbv_text_byte_offset(value, offset + count);"
  , "  uint8_t *data = sbv_text_alloc(ctx, last - first); memcpy(data, value.data + first, last - first);"
  , "  return sbv_string_borrow(data, last - first, count);"
  , "}"
  , ""
  , "static SString sbv_text_substring(sbv_text_ctx *ctx, SString value, int64_t offset, int64_t count)"
  , "{"
  , "  if (offset < 0 || count <= 0) return sbv_string_borrow(NULL, 0, 0);"
  , "  return sbv_text_substring_size(ctx, value, (size_t) offset, (size_t) count);"
  , "}"
  , ""
  , "static bool sbv_text_prefix_of(SString prefix, SString value)"
  , "{"
  , "  return prefix.byte_length <= value.byte_length"
  , "      && (prefix.byte_length == 0 || memcmp(prefix.data, value.data, prefix.byte_length) == 0);"
  , "}"
  , ""
  , "static bool sbv_text_suffix_of(SString suffix, SString value)"
  , "{"
  , "  return suffix.byte_length <= value.byte_length"
  , "      && (suffix.byte_length == 0 || memcmp(suffix.data, value.data + value.byte_length - suffix.byte_length, suffix.byte_length) == 0);"
  , "}"
  , ""
  , "static bool sbv_text_contains(SString value, SString part)"
  , "{"
  , "  if (part.byte_length == 0) return true;"
  , "  if (part.byte_length > value.byte_length) return false;"
  , "  for (size_t offset = 0; offset + part.byte_length <= value.byte_length; offset += sbv_text_width(value.data[offset]))"
  , "    if (memcmp(value.data + offset, part.data, part.byte_length) == 0) return true;"
  , "  return false;"
  , "}"
  , ""
  , "static int64_t sbv_text_index_of_size(SString value, SString part, size_t start)"
  , "{"
  , "  if (start > value.length) return -1;"
  , "  if (part.byte_length == 0) return start <= INT64_MAX ? (int64_t) start : -1;"
  , "  if (part.byte_length > value.byte_length) return -1;"
  , "  size_t character = start;"
  , "  for (size_t byte = sbv_text_byte_offset(value, start); byte + part.byte_length <= value.byte_length; ++character) {"
  , "    if (memcmp(value.data + byte, part.data, part.byte_length) == 0) return character <= INT64_MAX ? (int64_t) character : -1;"
  , "    byte += sbv_text_width(value.data[byte]);"
  , "  }"
  , "  return -1;"
  , "}"
  , ""
  , "static int64_t sbv_text_index_of(SString value, SString part, int64_t start)"
  , "{"
  , "  return start < 0 ? -1 : sbv_text_index_of_size(value, part, (size_t) start);"
  , "}"
  , ""
  , "static SString sbv_text_replace(sbv_text_ctx *ctx, SString value, SString source, SString replacement)"
  , "{"
  , "  const int64_t index = sbv_text_index_of_size(value, source, 0);"
  , "  if (index < 0) return value;"
  , "  const size_t first = sbv_text_byte_offset(value, (size_t) index);"
  , "  const size_t after = first + source.byte_length;"
  , "  const size_t retained = value.byte_length - source.byte_length;"
  , "  if (replacement.byte_length > SIZE_MAX - retained) abort();"
  , "  const size_t byte_length = retained + replacement.byte_length;"
  , "  uint8_t *data = sbv_text_alloc(ctx, byte_length);"
  , "  if (first != 0) memcpy(data, value.data, first);"
  , "  if (replacement.byte_length != 0) memcpy(data + first, replacement.data, replacement.byte_length);"
  , "  if (after != value.byte_length) memcpy(data + first + replacement.byte_length, value.data + after, value.byte_length - after);"
  , "  return sbv_string_borrow(data, byte_length, value.length - source.length + replacement.length);"
  , "}"
  , ""
  , "static SChar sbv_text_from_code(int64_t value)"
  , "{"
  , "  if (value < 0 || value > INT64_C(0x2ffff)) abort();"
  , "  return (SChar) value;"
  , "}"
  ]

-- | Runtime helpers used when 'SInteger' has a native lossy mapping.
nativeIntegerHelpers :: [String]
nativeIntegerHelpers =
  [""
  , "static int64_t sbv_text_to_nat(SString value)"
  , "{"
  , "  if (value.byte_length == 0) return -1;"
  , "  uint64_t result = 0;"
  , "  for (size_t i = 0; i < value.byte_length; ++i) {"
  , "    if (value.data[i] < UINT8_C(0x30) || value.data[i] > UINT8_C(0x39)) return -1;"
  , "    result = result * UINT64_C(10) + (value.data[i] - UINT8_C(0x30));"
  , "  }"
  , "  return (int64_t) result;"
  , "}"
  , ""
  , "static SString sbv_text_from_nat(sbv_text_ctx *ctx, int64_t value)"
  , "{"
  , "  if (value < 0) return sbv_string_borrow(NULL, 0, 0);"
  , "  char buffer[32];"
  , "  const int count = snprintf(buffer, sizeof buffer, \"%\" PRIu64, (uint64_t) value);"
  , "  uint8_t *data = sbv_text_alloc(ctx, (size_t) count); memcpy(data, buffer, (size_t) count);"
  , "  return sbv_string_borrow(data, (size_t) count, (size_t) count);"
  , "}"
  ]

-- | Runtime adapters used when 'SInteger' retains its exact GMP mapping.
exactIntegerRuntime :: [String]
exactIntegerRuntime =
  [""
  , "static bool sbv_text_mpz_to_size(SInteger value, size_t *result)"
  , "{"
  , "  if (mpz_sgn(value) < 0 || mpz_sizeinbase(value, 2) > sizeof(size_t) * CHAR_BIT) return false;"
  , "  size_t written = 0; *result = 0;"
  , "  (void) mpz_export(result, &written, -1, sizeof(*result), 0, 0, value);"
  , "  return true;"
  , "}"
  , ""
  , "static SChar sbv_text_nth_mpz(SString value, SInteger index)"
  , "{"
  , "  size_t converted;"
  , "  if (!sbv_text_mpz_to_size(index, &converted) || converted >= value.length) return UINT32_C(0);"
  , "  return sbv_text_decode(value.data + sbv_text_byte_offset(value, converted));"
  , "}"
  , ""
  , "static SString sbv_text_substring_mpz(sbv_text_ctx *ctx, SString value, SInteger offset, SInteger count)"
  , "{"
  , "  size_t converted_offset, converted_count;"
  , "  if (!sbv_text_mpz_to_size(offset, &converted_offset) || !sbv_text_mpz_to_size(count, &converted_count))"
  , "    return sbv_string_borrow(NULL, 0, 0);"
  , "  return sbv_text_substring_size(ctx, value, converted_offset, converted_count);"
  , "}"
  , ""
  , "static int64_t sbv_text_index_of_mpz(SString value, SString part, SInteger start)"
  , "{"
  , "  size_t converted;"
  , "  return sbv_text_mpz_to_size(start, &converted) ? sbv_text_index_of_size(value, part, converted) : -1;"
  , "}"
  , ""
  , "static SChar sbv_text_from_code_mpz(SInteger value)"
  , "{"
  , "  if (mpz_sgn(value) < 0 || mpz_cmp_ui(value, 0x2ffffUL) > 0) abort();"
  , "  return (SChar) mpz_get_ui(value);"
  , "}"
  , ""
  , "static SInteger sbv_text_to_nat_mpz(sbv_gmp_ctx *gmp_ctx, sbv_text_ctx *text_ctx, SString value)"
  , "{"
  , "  if (value.byte_length == 0) return sbv_gmp_integer_from_s64(gmp_ctx, -1);"
  , "  for (size_t i = 0; i < value.byte_length; ++i)"
  , "    if (value.data[i] < UINT8_C(0x30) || value.data[i] > UINT8_C(0x39)) return sbv_gmp_integer_from_s64(gmp_ctx, -1);"
  , "  char *digits = (char *) sbv_text_alloc(text_ctx, value.byte_length + 1);"
  , "  memcpy(digits, value.data, value.byte_length); digits[value.byte_length] = '\\0';"
  , "  return sbv_gmp_integer_const(gmp_ctx, digits);"
  , "}"
  , ""
  , "static SString sbv_text_from_nat_mpz(sbv_text_ctx *ctx, SInteger value)"
  , "{"
  , "  if (mpz_sgn(value) < 0) return sbv_string_borrow(NULL, 0, 0);"
  , "  const size_t count = mpz_sizeinbase(value, 10);"
  , "  uint8_t *data = sbv_text_alloc(ctx, count + 1);"
  , "  (void) mpz_get_str((char *) data, 10, value);"
  , "  return sbv_string_borrow(data, count, count);"
  , "}"
  ]
