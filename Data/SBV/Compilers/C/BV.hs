-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.BV
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Exact, portable lowering of non-native sized bit-vectors to C.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.BV
  ( isWideBV
  , wideBVKinds
  , wideBVTypeDecls
  , wideBVRuntime
  , wideBVConst
  , wideBVExpr
  , wideBVLookupInRange
  , wideBVLookupIndex
  , wideBVNormalize
  , wideBVPrint
  ) where

import Data.Bits                  (shiftL, shiftR, (.&.))
import Data.Char                  (toUpper)
import Data.List                  (intercalate, nub, stripPrefix, tails)
import qualified Data.Set as Set
import Numeric                    (showHex)

import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as P ((<>))

import Data.SBV.Core.Data

-- | True when a bit-vector cannot use the historical scalar C ABI. These
-- values are represented as little-endian arrays of 64-bit limbs.
isWideBV :: Kind -> Bool
isWideBV k = isBounded k
          && k /= KBounded False 1
          && intSizeOf k `notElem` [8, 16, 32, 64]

-- | The distinct non-native bit-vector kinds used by a program.
wideBVKinds :: Set.Set Kind -> [Kind]
wideBVKinds = filter isWideBV . Set.toAscList

-- | Type declarations and printing routines belonging in the public header.
wideBVTypeDecls :: [Kind] -> Doc
wideBVTypeDecls [] = empty
wideBVTypeDecls ks = text . unlines $
     ["/* Exact-width bit-vectors (least-significant limb first). */"
     , "#if defined(__GNUC__) || defined(__clang__)"
     , "#define SBV_CGEN_UNUSED __attribute__((unused))"
     , "#else"
     , "#define SBV_CGEN_UNUSED"
     , "#endif"]
  ++ concatMap decl ks
 where decl k = ["#ifndef " ++ guard k
                , "#define " ++ guard k
                , "typedef struct { uint64_t limb[" ++ show (limbs k) ++ "]; } " ++ cType k ++ ";"
                , "static inline SBV_CGEN_UNUSED void " ++ prefix k ++ "_fprint(FILE *stream, " ++ cType k ++ " value)"
                , "{"
                , "  size_t i = " ++ show (limbs k) ++ ";"
                , "  fputs(\"0x\", stream);"
                , "  while (i-- > 0) { fprintf(stream, \"%016\" PRIx64, value.limb[i]); }"
                , "}"
                , "#endif"
                , ""]

       guard k = "SBV_BV_" ++ map toUpper (tag k) ++ "_DEFINED"

-- | Runtime routines for each used exact-width type, plus the cross-width
-- helpers demanded by extracts, joins, extensions, and casts in the DAG.
wideBVRuntime :: [Kind] -> [(SV, SBVExpr)] -> Doc
wideBVRuntime [] _     = empty
wideBVRuntime ks asgns = text . unlines . map markUnused $
     ["/* Exact-width bit-vector runtime. All arithmetic is modulo the declared width. */", ""]
  ++ concatMap coreRuntime ks
  ++ concatMap specialRuntime (nub (concatMap specials asgns))
 where specials (sv, SBVApp op args) = case op of
         Extract hi lo                  -> [SpecialExtract (kindOf (headArg "Extract" args)) hi lo (kindOf sv)]
         Join                           -> case args of
                                             [a, b] -> [SpecialJoin (kindOf a) (kindOf b) (kindOf sv)]
                                             _      -> badArity "Join" args
         ZeroExtend _                   -> [SpecialConvert False (kindOf (headArg "ZeroExtend" args)) (kindOf sv)]
         SignExtend _                   -> [SpecialConvert True  (kindOf (headArg "SignExtend" args)) (kindOf sv)]
         KindCast fr to
           | isBounded fr && isBounded to -> [SpecialConvert (hasSign fr) fr to]
         IEEEFP (FP_Reinterpret fr to)
           | isBounded fr && isBounded to -> [SpecialConvert False fr to]
         _                              -> []

       specialRuntime s = case s of
         SpecialExtract fr hi lo to -> conversionRuntime (extractName fr hi lo to) False lo fr to
         SpecialJoin a b to          -> joinRuntime a b to
         SpecialConvert sign fr to   -> conversionRuntime (convertName sign fr to) sign 0 fr to

       markUnused line
         | Just rest <- stripPrefix "static inline " line = "static inline SBV_CGEN_UNUSED " ++ rest
         | otherwise                                      = line

-- | Render a constant as a C99 compound literal.
wideBVConst :: Kind -> Integer -> Maybe Doc
wideBVConst k i
  | isWideBV k = Just . text $ "(" ++ cType k ++ "){{" ++ intercalate ", " (map word [0 .. limbs k - 1]) ++ "}}"
  | True       = Nothing
 where normalized = i `mod` (2 ^ intSizeOf k)
       word n     = u64 $ (normalized `shiftR` (64 * n)) .&. ((1 `shiftL` 64) - 1)

-- | Lower an operation involving a non-native bit-vector. A 'Nothing' result
-- means that the legacy scalar lowering should handle the operation.
wideBVExpr :: Op -> [SV] -> Kind -> [Doc] -> Maybe Doc
wideBVExpr op svs resultKind args
  | not (isWideBV resultKind || any (isWideBV . kindOf) svs)
  = Nothing
  | LkUp{} <- op
  = Nothing
  | Uninterpreted{} <- op
  = Nothing
  | True
  = Just $ case (op, args, svs) of
      (Label _                       , [a]      , _)      -> a
      (Plus                          , [a, b]   , _)      -> call "add" [a, b]
      (Minus                         , [a, b]   , _)      -> call "sub" [a, b]
      (Times                         , [a, b]   , _)      -> call "mul" [a, b]
      (UNeg                          , [a]      , _)      -> call "neg" [a]
      (Abs                           , [a]      , _)      -> call "abs" [a]
      (And                           , [a, b]   , _)      -> call "and" [a, b]
      (Or                            , [a, b]   , _)      -> call "or" [a, b]
      (XOr                           , [a, b]   , _)      -> call "xor" [a, b]
      (Not                           , [a]      , _)      -> call "not" [a]
      (Equal _                       , [a, b]   , x:_)    -> argCall x "eq" [a, b]
      (NotEqual                      , as       , x:_)    -> fsep $ punctuate (text " &&")
                                                                 [text "!" P.<> parens (argCall x "eq" [a, b])
                                                                 | (a:rest) <- tails as, b <- rest]
      (LessThan                      , [a, b]   , x:_)    -> argCall x "lt" [a, b]
      (GreaterThan                   , [a, b]   , x:_)    -> argCall x "lt" [b, a]
      (LessEq                        , [a, b]   , x:_)    -> text "!" P.<> parens (argCall x "lt" [b, a])
      (GreaterEq                     , [a, b]   , x:_)    -> text "!" P.<> parens (argCall x "lt" [a, b])
      (Ite                           , [c, a, b], _)      -> c <+> text "?" <+> a <+> text ":" <+> b
      (Quot                          , [a, b]   , _)      -> call "quot" [a, b]
      (Rem                           , [a, b]   , _)      -> call "rem" [a, b]
      (Shl                           , [a, n]   , x:_)    -> argCall x "shl" [a, argCall x "shift_amount" [n]]
      (Shr                           , [a, n]   , x:_)    -> argCall x (if hasSign x then "ashr" else "lshr") [a, argCall x "shift_amount" [n]]
      (Rol n                         , [a]      , _)      -> call "rotl" [a, integer (fromIntegral n)]
      (Ror n                         , [a]      , _)      -> call "rotr" [a, integer (fromIntegral n)]
      (Extract hi lo                 , [a]      , x:_)    -> namedCall (extractName (kindOf x) hi lo resultKind) [a]
      (Join                          , [a, b]   , [x, y]) -> namedCall (joinName (kindOf x) (kindOf y) resultKind) [a, b]
      (ZeroExtend _                  , [a]      , x:_)    -> namedCall (convertName False (kindOf x) resultKind) [a]
      (SignExtend _                  , [a]      , x:_)    -> namedCall (convertName True  (kindOf x) resultKind) [a]
      (KindCast fr to                , [a]      , _)      -> namedCall (convertName (hasSign fr) fr to) [a]
      (OverflowOp ov                 , as       , x:_)    -> argCall x (overflowName ov) as
      (IEEEFP (FP_Reinterpret fr to) , [a]      , _)
          | isBounded fr || isBounded to                  -> namedCall (convertName False fr to) [a]
      _                                                   -> error $ "SBV->C: exact bit-vector lowering does not yet support " ++ show op
                                                                  ++ " with argument kinds " ++ show (map kindOf svs)
                                                                  ++ " and result kind " ++ show resultKind
 where call suffix       = namedCall (prefix resultKind ++ "_" ++ suffix)
       argCall sv suffix = namedCall (prefix (kindOf sv) ++ "_" ++ suffix)

-- | Print a wide value without requiring a printf conversion specifier.
wideBVPrint :: Kind -> Doc -> Doc
wideBVPrint k value = namedCall (prefix k ++ "_fprint") [text "stdout", value]

-- | Test whether a wide bit-vector is a valid zero-based index below the
-- supplied table length.
wideBVLookupInRange :: Kind -> Int -> Doc -> Doc
wideBVLookupInRange k len value = namedCall (prefix k ++ "_index_in_range") [value, integer (fromIntegral len)]

-- | Convert a wide bit-vector known to be in range to a native C table index.
wideBVLookupIndex :: Kind -> Doc -> Doc
wideBVLookupIndex k value = namedCall (prefix k ++ "_index") [value]

-- | Canonicalize an externally supplied wide value by clearing unused bits in
-- its most-significant limb.
wideBVNormalize :: Kind -> Doc -> Doc
wideBVNormalize k value = namedCall (prefix k ++ "_norm") [value]

-- | Cross-width helpers discovered while walking the symbolic DAG.
data Special = SpecialExtract Kind Int Int Kind
             | SpecialJoin    Kind Kind Kind
             | SpecialConvert Bool Kind Kind
             deriving (Eq)

-- | Emit the complete modular-arithmetic runtime for one bit-vector kind.
coreRuntime :: Kind -> [String]
coreRuntime k =
  ["static inline " ++ ty ++ " " ++ p ++ "_zero(void)"
  , "{"
  , "  " ++ ty ++ " r = {{0}};"
  , "  return r;"
  , "}"
  , ""
  , "static inline " ++ ty ++ " " ++ p ++ "_norm(" ++ ty ++ " a)"
  , "{"
  , "  a.limb[" ++ show (n - 1) ++ "] &= " ++ u64 mask ++ ";"
  , "  return a;"
  , "}"
  , ""
  , "static inline bool " ++ p ++ "_get(" ++ ty ++ " a, uint64_t bit)"
  , "{"
  , "  return bit < " ++ show w ++ " && ((a.limb[bit / 64] >> (bit % 64)) & UINT64_C(1)) != 0;"
  , "}"
  , ""
  , "static inline void " ++ p ++ "_set(" ++ ty ++ " *a, uint64_t bit, bool value)"
  , "{"
  , "  const uint64_t m = UINT64_C(1) << (bit % 64);"
  , "  if (value) { a->limb[bit / 64] |= m; } else { a->limb[bit / 64] &= ~m; }"
  , "}"
  , ""
  , "static inline bool " ++ p ++ "_is_zero(" ++ ty ++ " a)"
  , "{"
  , "  uint64_t v = 0;"
  , "  size_t i;"
  , "  for (i = 0; i < " ++ show n ++ "; ++i) { v |= a.limb[i]; }"
  , "  return v == 0;"
  , "}"
  , ""
  , "static inline bool " ++ p ++ "_eq(" ++ ty ++ " a, " ++ ty ++ " b)"
  , "{"
  , "  uint64_t v = 0;"
  , "  size_t i;"
  , "  for (i = 0; i < " ++ show n ++ "; ++i) { v |= a.limb[i] ^ b.limb[i]; }"
  , "  return v == 0;"
  , "}"
  , ""
  , "static inline int " ++ p ++ "_cmpu(" ++ ty ++ " a, " ++ ty ++ " b)"
  , "{"
  , "  size_t i = " ++ show n ++ ";"
  , "  while (i-- > 0) { if (a.limb[i] < b.limb[i]) return -1; if (a.limb[i] > b.limb[i]) return 1; }"
  , "  return 0;"
  , "}"
  , ""
  , "static inline bool " ++ p ++ "_lt(" ++ ty ++ " a, " ++ ty ++ " b)"
  , "{"
  ]
  ++ signedCompare
  ++ ["}"
     , ""
     , "static inline " ++ ty ++ " " ++ p ++ "_add(" ++ ty ++ " a, " ++ ty ++ " b)"
     , "{"
     , "  " ++ ty ++ " r;"
     , "  uint64_t carry = 0;"
     , "  size_t i;"
     , "  for (i = 0; i < " ++ show n ++ "; ++i) {"
     , "    uint64_t s = a.limb[i] + b.limb[i];"
     , "    uint64_t c1 = s < a.limb[i];"
     , "    uint64_t t = s + carry;"
     , "    uint64_t c2 = t < s;"
     , "    r.limb[i] = t; carry = c1 | c2;"
     , "  }"
     , "  return " ++ p ++ "_norm(r);"
     , "}"
     , ""
     , "static inline uint64_t " ++ p ++ "_index(" ++ ty ++ " a)"
     , "{"
     , "  return a.limb[0];"
     , "}"
     , ""
     , "static inline bool " ++ p ++ "_index_in_range(" ++ ty ++ " a, uint64_t limit)"
     , "{"
     , "  size_t i;"
     , "  for (i = 1; i < " ++ show n ++ "; ++i) if (a.limb[i] != UINT64_C(0)) return false;"
     , "  return a.limb[0] < limit;"
     , "}"
     , ""
     , "static inline " ++ ty ++ " " ++ p ++ "_sub(" ++ ty ++ " a, " ++ ty ++ " b)"
     , "{"
     , "  " ++ ty ++ " r;"
     , "  uint64_t borrow = 0;"
     , "  size_t i;"
     , "  for (i = 0; i < " ++ show n ++ "; ++i) {"
     , "    uint64_t d = a.limb[i] - b.limb[i];"
     , "    uint64_t b1 = a.limb[i] < b.limb[i];"
     , "    uint64_t t = d - borrow;"
     , "    uint64_t b2 = d < borrow;"
     , "    r.limb[i] = t; borrow = b1 | b2;"
     , "  }"
     , "  return " ++ p ++ "_norm(r);"
     , "}"
     , ""
     , "static inline " ++ ty ++ " " ++ p ++ "_not(" ++ ty ++ " a)"
     , "{"
     , "  size_t i;"
     , "  for (i = 0; i < " ++ show n ++ "; ++i) { a.limb[i] = ~a.limb[i]; }"
     , "  return " ++ p ++ "_norm(a);"
     , "}"
     , ""
     , "static inline " ++ ty ++ " " ++ p ++ "_neg(" ++ ty ++ " a)"
     , "{"
     , "  " ++ ty ++ " one = " ++ p ++ "_zero(); one.limb[0] = 1;"
     , "  return " ++ p ++ "_add(" ++ p ++ "_not(a), one);"
     , "}"
     , ""
     ]
  ++ concatMap bitwise [("and", "&"), ("or", "|"), ("xor", "^")]
  ++ ["static inline " ++ ty ++ " " ++ p ++ "_shl(" ++ ty ++ " a, uint64_t amount)"
     , "{"
     , "  " ++ ty ++ " r = " ++ p ++ "_zero();"
     , "  uint64_t ws, bs; size_t i;"
     , "  if (amount >= " ++ show w ++ ") return r;"
     , "  ws = amount / 64; bs = amount % 64;"
     , "  for (i = " ++ show n ++ "; i-- > ws;) {"
     , "    r.limb[i] = a.limb[i - ws] << bs;"
     , "    if (bs != 0 && i > ws) r.limb[i] |= a.limb[i - ws - 1] >> (64 - bs);"
     , "  }"
     , "  return " ++ p ++ "_norm(r);"
     , "}"
     , ""
     , "static inline " ++ ty ++ " " ++ p ++ "_lshr(" ++ ty ++ " a, uint64_t amount)"
     , "{"
     , "  " ++ ty ++ " r = " ++ p ++ "_zero();"
     , "  uint64_t ws, bs; size_t i;"
     , "  if (amount >= " ++ show w ++ ") return r;"
     , "  ws = amount / 64; bs = amount % 64;"
     , "  for (i = 0; i + ws < " ++ show n ++ "; ++i) {"
     , "    r.limb[i] = a.limb[i + ws] >> bs;"
     , "    if (bs != 0 && i + ws + 1 < " ++ show n ++ ") r.limb[i] |= a.limb[i + ws + 1] << (64 - bs);"
     , "  }"
     , "  return " ++ p ++ "_norm(r);"
     , "}"
     , ""
     , "static inline " ++ ty ++ " " ++ p ++ "_ashr(" ++ ty ++ " a, uint64_t amount)"
     , "{"
     , "  " ++ ty ++ " r = " ++ p ++ "_zero(); uint64_t i;"
     , "  const bool sign = " ++ p ++ "_get(a, " ++ show (w - 1) ++ ");"
     , "  for (i = 0; i < " ++ show w ++ "; ++i) { " ++ p ++ "_set(&r, i, i + amount < " ++ show w ++ " ? " ++ p ++ "_get(a, i + amount) : sign); }"
     , "  return r;"
     , "}"
     , ""
     , "static inline uint64_t " ++ p ++ "_shift_amount(" ++ ty ++ " a)"
     , "{"
     , "  size_t i;"
     , "  for (i = 1; i < " ++ show n ++ "; ++i) if (a.limb[i] != 0) return " ++ show w ++ ";"
     , "  return a.limb[0] < " ++ show w ++ " ? a.limb[0] : " ++ show w ++ ";"
     , "}"
     , ""
     , "static inline " ++ ty ++ " " ++ p ++ "_rotl(" ++ ty ++ " a, uint64_t amount)"
     , "{"
     , "  amount %= " ++ show w ++ ";"
     , "  return amount == 0 ? a : " ++ p ++ "_or(" ++ p ++ "_shl(a, amount), " ++ p ++ "_lshr(a, " ++ show w ++ " - amount));"
     , "}"
     , ""
     , "static inline " ++ ty ++ " " ++ p ++ "_rotr(" ++ ty ++ " a, uint64_t amount)"
     , "{"
     , "  amount %= " ++ show w ++ ";"
     , "  return amount == 0 ? a : " ++ p ++ "_or(" ++ p ++ "_lshr(a, amount), " ++ p ++ "_shl(a, " ++ show w ++ " - amount));"
     , "}"
     , ""
     , "static inline " ++ ty ++ " " ++ p ++ "_mul(" ++ ty ++ " a, " ++ ty ++ " b)"
     , "{"
     , "  " ++ ty ++ " r = " ++ p ++ "_zero(); uint64_t bit;"
     , "  for (bit = 0; bit < " ++ show w ++ "; ++bit) {"
     , "    " ++ ty ++ " selected; uint64_t mask = UINT64_C(0) - (uint64_t) " ++ p ++ "_get(b, bit); size_t i;"
     , "    for (i = 0; i < " ++ show n ++ "; ++i) selected.limb[i] = a.limb[i] & mask;"
     , "    r = " ++ p ++ "_add(r, selected); a = " ++ p ++ "_shl(a, 1);"
     , "  }"
     , "  return r;"
     , "}"
     , ""
     , "static inline void " ++ p ++ "_udivrem(" ++ ty ++ " a, " ++ ty ++ " b, " ++ ty ++ " *q, " ++ ty ++ " *r)"
     , "{"
     , "  uint64_t bit; *q = " ++ p ++ "_zero(); *r = " ++ p ++ "_zero();"
     , "  if (" ++ p ++ "_is_zero(b)) { *r = a; return; }"
     , "  for (bit = " ++ show w ++ "; bit-- > 0;) {"
     , "    *r = " ++ p ++ "_shl(*r, 1); " ++ p ++ "_set(r, 0, " ++ p ++ "_get(a, bit));"
     , "    if (" ++ p ++ "_cmpu(*r, b) >= 0) { *r = " ++ p ++ "_sub(*r, b); " ++ p ++ "_set(q, bit, true); }"
     , "  }"
     , "}"
     , ""
     ]
  ++ division
  ++ ["static inline " ++ ty ++ " " ++ p ++ "_abs(" ++ ty ++ " a)"
     , "{"
     , if hasSign k then "  return " ++ p ++ "_get(a, " ++ show (w - 1) ++ ") ? " ++ p ++ "_neg(a) : a;" else "  return a;"
     , "}"
     , ""
     ]
  ++ overflowRuntime
 where ty   = cType k
       p    = prefix k
       w    = intSizeOf k
       n    = limbs k
       mask = topMask k

       signedCompare
         | hasSign k = ["  const bool sa = " ++ p ++ "_get(a, " ++ show (w - 1) ++ ");"
                        , "  const bool sb = " ++ p ++ "_get(b, " ++ show (w - 1) ++ ");"
                        , "  return sa != sb ? sa : " ++ p ++ "_cmpu(a, b) < 0;"]
         | True       = ["  return " ++ p ++ "_cmpu(a, b) < 0;"]

       bitwise (nm, op) =
         ["static inline " ++ ty ++ " " ++ p ++ "_" ++ nm ++ "(" ++ ty ++ " a, " ++ ty ++ " b)"
         , "{"
         , "  size_t i;"
         , "  for (i = 0; i < " ++ show n ++ "; ++i) { a.limb[i] " ++ op ++ "= b.limb[i]; }"
         , "  return " ++ p ++ "_norm(a);"
         , "}"
         , ""]

       division
         | hasSign k =
            ["static inline " ++ ty ++ " " ++ p ++ "_quot(" ++ ty ++ " a, " ++ ty ++ " b)"
            , "{"
            , "  " ++ ty ++ " q, r; const bool sa = " ++ p ++ "_get(a, " ++ show (w - 1) ++ "); const bool sb = " ++ p ++ "_get(b, " ++ show (w - 1) ++ ");"
            , "  " ++ p ++ "_udivrem(sa ? " ++ p ++ "_neg(a) : a, sb ? " ++ p ++ "_neg(b) : b, &q, &r);"
            , "  return sa != sb ? " ++ p ++ "_neg(q) : q;"
            , "}"
            , ""
            , "static inline " ++ ty ++ " " ++ p ++ "_rem(" ++ ty ++ " a, " ++ ty ++ " b)"
            , "{"
            , "  " ++ ty ++ " q, r; const bool sa = " ++ p ++ "_get(a, " ++ show (w - 1) ++ "); const bool sb = " ++ p ++ "_get(b, " ++ show (w - 1) ++ ");"
            , "  " ++ p ++ "_udivrem(sa ? " ++ p ++ "_neg(a) : a, sb ? " ++ p ++ "_neg(b) : b, &q, &r);"
            , "  return sa ? " ++ p ++ "_neg(r) : r;"
            , "}"
            , ""]
         | True =
            ["static inline " ++ ty ++ " " ++ p ++ "_quot(" ++ ty ++ " a, " ++ ty ++ " b)"
            , "{ " ++ ty ++ " q, r; " ++ p ++ "_udivrem(a, b, &q, &r); return q; }"
            , ""
            , "static inline " ++ ty ++ " " ++ p ++ "_rem(" ++ ty ++ " a, " ++ ty ++ " b)"
            , "{ " ++ ty ++ " q, r; " ++ p ++ "_udivrem(a, b, &q, &r); return r; }"
            , ""]

       overflowRuntime =
         ["static inline bool " ++ p ++ "_is_min(" ++ ty ++ " a)"
         , "{"
         , "  " ++ ty ++ " m = " ++ p ++ "_zero();"
         , "  " ++ p ++ "_set(&m, " ++ show (w - 1) ++ ", true);"
         , "  return " ++ p ++ "_eq(a, m);"
         , "}"
         , ""
         , "static inline bool " ++ p ++ "_uaddo(" ++ ty ++ " a, " ++ ty ++ " b)"
         , "{"
         , "  return " ++ p ++ "_cmpu(" ++ p ++ "_add(a, b), a) < 0;"
         , "}"
         , ""
         , "static inline bool " ++ p ++ "_saddo(" ++ ty ++ " a, " ++ ty ++ " b)"
         , "{"
         , "  const " ++ ty ++ " r = " ++ p ++ "_add(a, b);"
         , "  const bool sa = " ++ p ++ "_get(a, " ++ show (w - 1) ++ ");"
         , "  const bool sb = " ++ p ++ "_get(b, " ++ show (w - 1) ++ ");"
         , "  const bool sr = " ++ p ++ "_get(r, " ++ show (w - 1) ++ ");"
         , "  return sa == sb && sa != sr;"
         , "}"
         , ""
         , "static inline bool " ++ p ++ "_usubo(" ++ ty ++ " a, " ++ ty ++ " b)"
         , "{"
         , "  return " ++ p ++ "_cmpu(a, b) < 0;"
         , "}"
         , ""
         , "static inline bool " ++ p ++ "_ssubo(" ++ ty ++ " a, " ++ ty ++ " b)"
         , "{"
         , "  const " ++ ty ++ " r = " ++ p ++ "_sub(a, b);"
         , "  const bool sa = " ++ p ++ "_get(a, " ++ show (w - 1) ++ ");"
         , "  const bool sb = " ++ p ++ "_get(b, " ++ show (w - 1) ++ ");"
         , "  const bool sr = " ++ p ++ "_get(r, " ++ show (w - 1) ++ ");"
         , "  return sa != sb && sa != sr;"
         , "}"
         , ""
         , "static inline bool " ++ p ++ "_umulo(" ++ ty ++ " a, " ++ ty ++ " b)"
         , "{"
         , "  " ++ ty ++ " q, r;"
         , "  if (" ++ p ++ "_is_zero(b)) return false;"
         , "  " ++ p ++ "_udivrem(" ++ p ++ "_mul(a, b), b, &q, &r);"
         , "  return !" ++ p ++ "_eq(q, a);"
         , "}"
         , ""
         , "static inline bool " ++ p ++ "_smulo(" ++ ty ++ " a, " ++ ty ++ " b)"
         , "{"
         , "  " ++ ty ++ " q, r, limit = " ++ p ++ "_zero();"
         , "  const bool sa = " ++ p ++ "_get(a, " ++ show (w - 1) ++ ");"
         , "  const bool sb = " ++ p ++ "_get(b, " ++ show (w - 1) ++ ");"
         , "  const bool negative = sa != sb;"
         , "  uint64_t bit;"
         , "  if (sa) a = " ++ p ++ "_neg(a);"
         , "  if (sb) b = " ++ p ++ "_neg(b);"
         , "  if (" ++ p ++ "_is_zero(a) || " ++ p ++ "_is_zero(b)) return false;"
         , "  if (negative) " ++ p ++ "_set(&limit, " ++ show (w - 1) ++ ", true);"
         , "  else for (bit = 0; bit < " ++ show (w - 1) ++ "; ++bit) " ++ p ++ "_set(&limit, bit, true);"
         , "  " ++ p ++ "_udivrem(limit, b, &q, &r);"
         , "  return " ++ p ++ "_cmpu(a, q) > 0;"
         , "}"
         , ""
         , "static inline bool " ++ p ++ "_sdivo(" ++ ty ++ " a, " ++ ty ++ " b)"
         , "{"
         , "  return " ++ p ++ "_is_min(a) && " ++ p ++ "_eq(b, " ++ p ++ "_not(" ++ p ++ "_zero()));"
         , "}"
         , ""
         , "static inline bool " ++ p ++ "_snego(" ++ ty ++ " a)"
         , "{"
         , "  return " ++ p ++ "_is_min(a);"
         , "}"
         , ""]

-- | Emit a bit-preserving extraction, extension, or integral conversion.
conversionRuntime :: String -> Bool -> Int -> Kind -> Kind -> [String]
conversionRuntime nm signExtend sourceOffset fr to =
  ["static inline " ++ cType to ++ " " ++ nm ++ "(" ++ cType fr ++ " a)"
  , "{"
  , "  " ++ cType to ++ " r = " ++ zeroValue to ++ ";"
  , "  uint64_t i;"
  , "  for (i = 0; i < " ++ show copied ++ "; ++i) { " ++ setBit to "r" "i" (getBit fr "a" (offset "i")) ++ " }"
  ]
  ++ extension
  ++ ["  return " ++ normalize to "r" ++ ";"
     , "}"
     , ""]
 where available = max 0 (bitWidth fr - sourceOffset)
       copied    = min available (bitWidth to)
       offset i  = if sourceOffset == 0 then i else i ++ " + " ++ show sourceOffset
       extension
         | signExtend && bitWidth to > copied =
             ["  if (" ++ getBit fr "a" (show (bitWidth fr - 1)) ++ ") for (i = " ++ show copied ++ "; i < " ++ show (bitWidth to) ++ "; ++i) { " ++ setBit to "r" "i" "true" ++ " }"]
         | True                                      = []

-- | Emit concatenation code for a particular pair of operand kinds.
joinRuntime :: Kind -> Kind -> Kind -> [String]
joinRuntime a b to =
  ["static inline " ++ cType to ++ " " ++ joinName a b to ++ "(" ++ cType a ++ " high, " ++ cType b ++ " low)"
  , "{"
  , "  " ++ cType to ++ " r = " ++ zeroValue to ++ "; uint64_t i;"
  , "  for (i = 0; i < " ++ show (bitWidth b) ++ "; ++i) { " ++ setBit to "r" "i" (getBit b "low" "i") ++ " }"
  , "  for (i = 0; i < " ++ show (bitWidth a) ++ "; ++i) { " ++ setBit to "r" ("i + " ++ show (bitWidth b)) (getBit a "high" "i") ++ " }"
  , "  return " ++ normalize to "r" ++ ";"
  , "}"
  , ""]

-- | Render a target-independent bit read from a scalar or limb value.
getBit :: Kind -> String -> String -> String
getBit k value bit
  | isWideBV k                  = prefix k ++ "_get(" ++ value ++ ", " ++ bit ++ ")"
  | isBoolean k || isBounded k = "((((uint64_t) " ++ value ++ ") >> (" ++ bit ++ ")) & UINT64_C(1)) != 0"
  | otherwise                  = error $ "SBV->C: Cannot extract bits from " ++ show k

-- | Render a target-independent bit update to a scalar or limb value.
setBit :: Kind -> String -> String -> String -> String
setBit k value bit bitValue
  | isWideBV k                  = prefix k ++ "_set(&" ++ value ++ ", " ++ bit ++ ", " ++ bitValue ++ ");"
  | isBoolean k || isBounded k = value ++ " = (" ++ cType k ++ ") ((uint64_t) " ++ value ++ " | ((uint64_t) (" ++ bitValue ++ ") << (" ++ bit ++ ")));"
  | otherwise                  = error $ "SBV->C: Cannot set bits in " ++ show k

-- | Render the zero value for a scalar or limb representation.
zeroValue :: Kind -> String
zeroValue k
  | isWideBV k                  = prefix k ++ "_zero()"
  | isBoolean k || isBounded k = "(" ++ cType k ++ ") 0"
  | otherwise                  = error $ "SBV->C: Cannot construct a zero of " ++ show k

-- | Render canonicalization for a scalar or limb representation.
normalize :: Kind -> String -> String
normalize k value
  | isWideBV k                  = prefix k ++ "_norm(" ++ value ++ ")"
  | isBoolean k || isBounded k = value
  | otherwise                  = error $ "SBV->C: Cannot normalize " ++ show k

-- | Construct the collision-free name of an extraction helper.
extractName :: Kind -> Int -> Int -> Kind -> String
extractName fr hi lo to = "sbv_bv_extract_" ++ tag fr ++ "_" ++ show hi ++ "_" ++ show lo ++ "_" ++ tag to

-- | Construct the collision-free name of a concatenation helper.
joinName :: Kind -> Kind -> Kind -> String
joinName a b to = "sbv_bv_join_" ++ tag a ++ "_" ++ tag b ++ "_" ++ tag to

-- | Construct the collision-free name of an extension/conversion helper.
convertName :: Bool -> Kind -> Kind -> String
convertName sign fr to = "sbv_bv_" ++ (if sign then "sext_" else "zext_") ++ tag fr ++ "_" ++ tag to

-- | Render a C function call.
namedCall :: String -> [Doc] -> Doc
namedCall nm args = text nm P.<> parens (fsep (punctuate comma args))

-- | Select the first operation argument, reporting an internal arity error.
headArg :: String -> [a] -> a
headArg _ (a:_) = a
headArg nm []    = error $ "SBV->C: " ++ nm ++ " unexpectedly has no arguments"

-- | Report an internal arity error for an operation.
badArity :: String -> [a] -> b
badArity nm _ = error $ "SBV->C: " ++ nm ++ " has an unexpected arity"

-- | Return the generated helper suffix for an overflow predicate.
overflowName :: OvOp -> String
overflowName (PlusOv False) = "uaddo"
overflowName (PlusOv True)  = "saddo"
overflowName (SubOv  False) = "usubo"
overflowName (SubOv  True)  = "ssubo"
overflowName (MulOv  False) = "umulo"
overflowName (MulOv  True)  = "smulo"
overflowName DivOv          = "sdivo"
overflowName NegOv          = "snego"

-- | Return the logical bit width used by the C representation. Unlike
-- 'intSizeOf', this is defined for 'KBool', which occupies one logical bit.
bitWidth :: Kind -> Int
bitWidth k
  | isBoolean k = 1
  | otherwise   = intSizeOf k

-- | Return the number of 64-bit limbs needed by a kind.
limbs :: Kind -> Int
limbs k = (intSizeOf k + 63) `div` 64

-- | Return the mask for the final limb of a canonical value.
topMask :: Kind -> Integer
topMask k
  | r == 0    = (1 `shiftL` 64) - 1
  | otherwise = (1 `shiftL` r) - 1
 where r = intSizeOf k `mod` 64

-- | Return the C type name used for a bit-vector kind.
cType :: Kind -> String
cType KBool               = "SBool"
cType (KBounded False 1)  = "SBool"
cType (KBounded False w)  = "SWord" ++ show w
cType (KBounded True  w)  = "SInt"  ++ show w
cType k                   = error $ "SBV->C: Expected a C bit-vector type, received " ++ show k

-- | Return the compact signedness-and-width tag used in generated names.
tag :: Kind -> String
tag KBool               = "u1"
tag (KBounded False w)  = "u" ++ show w
tag (KBounded True  w)  = "s" ++ show w
tag k                   = error $ "SBV->C: Expected a bit-vector tag, received " ++ show k

-- | Return the namespace prefix for helpers belonging to a kind.
prefix :: Kind -> String
prefix k = "sbv_bv_" ++ tag k

-- | Render an integer as a padded, portable C @uint64_t@ literal.
u64 :: Integer -> String
u64 i = "UINT64_C(0x" ++ pad 16 (showHex i "") ++ ")"
 where pad n s = replicate (n - length s) '0' ++ s
