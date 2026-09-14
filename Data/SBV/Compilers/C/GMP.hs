-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.GMP
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Exact GMP-backed lowering of unbounded integers, reals, and rationals to C.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.GMP
  ( isExactGMPKind
  , gmpEqual
  , gmpTypeDecls
  , gmpRuntime
  , gmpConst
  , gmpExpr
  , gmpPrint
  , gmpSet
  , gmpOutputType
  , gmpArrayType
  , gmpDriverInitialize
  , gmpDriverInit
  , gmpDriverClear
  , gmpContextStart
  , gmpContextEnd
  ) where

import Data.Bits                       (shiftL)
import Data.List                       (nub, stripPrefix, tails)
import Data.Ratio                      (denominator, numerator)
import qualified Data.Set as Set
import qualified Data.Text as T
import Numeric                         (showHex)

import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as P ((<>))

import Data.SBV.Compilers.C.BV         (isWideBV, mappedIntegerKind)
import Data.SBV.Compilers.C.Lowering   (CLowering, CRequirement(..), expressionLowering)
import Data.SBV.Compilers.CodeGen      (CgConfig(..), CgSRealType(..))
import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic          (NROp(..))

-- | Test whether a kind uses the exact GMP representation under this
-- configuration. Supplying 'Data.SBV.Tools.CodeGen.cgIntegerSize' or
-- 'Data.SBV.Tools.CodeGen.cgSRealType' selects the
-- historical lossy representation for 'KUnbounded' or 'KReal'; 'KRational'
-- is always exact.
isExactGMPKind :: CgConfig -> Kind -> Bool
isExactGMPKind cfg KUnbounded = case cgInteger cfg of
                                  Nothing -> True
                                  Just{}  -> False
isExactGMPKind cfg KReal      = case cgReal cfg of
                                  Nothing -> True
                                  Just{}  -> False
isExactGMPKind _   KRational  = True
isExactGMPKind _   _          = False

-- | Compare two exact GMP-backed values for equality.
gmpEqual :: Kind -> Doc -> Doc -> Doc
gmpEqual kind left right = parens $ namedCall (kindPrefix kind ++ "cmp") [left, right] <+> text "==" <+> text "0"

-- | Declare the GMP-backed public C types required by the supplied kinds.
-- Inputs are borrowed read-only pointers. Outputs and exact return parameters
-- are caller-initialized mutable GMP pointers.
gmpTypeDecls :: CgConfig -> Set.Set Kind -> Doc
gmpTypeDecls cfg kinds
  | not needsExactInteger && not needsExactQuotient = empty
  | True                                            = text . unlines $
      ["/* Exact integers, reals, and rationals. Inputs are borrowed; scalar outputs are caller-initialized. */"
      , "/* Initialize each scalar/group output with mpz_init or mpq_init; clear it after its last use. */"
      , "/* Aggregate outputs instead receive fresh owned values, including any embedded GMP fields. */"
      , "#include <gmp.h>"
      , "#ifndef SBV_CGEN_UNUSED"
      , "#if defined(__GNUC__) || defined(__clang__)"
      , "#define SBV_CGEN_UNUSED __attribute__((unused))"
      , "#else"
      , "#define SBV_CGEN_UNUSED"
      , "#endif"
      , "#endif"]
   ++ integerDecls
   ++ realDecls
   ++ rationalDecls
   ++ [""]
 where needsExactInteger  = isExactGMPKind cfg KUnbounded && KUnbounded `Set.member` kinds
       needsExactReal     = isExactGMPKind cfg KReal      && KReal      `Set.member` kinds
       needsRational      = KRational `Set.member` kinds
       needsExactQuotient = needsExactReal || needsRational

       integerDecls
         | needsExactInteger = [ "#ifndef SBV_GMP_INTEGER_DEFINED"
                               , "#define SBV_GMP_INTEGER_DEFINED"
                               , "typedef mpz_srcptr SInteger;"
                               , "#endif"
                               ]
         | True              = []

       realDecls
         | needsExactReal = [ "#ifndef SBV_GMP_REAL_DEFINED"
                            , "#define SBV_GMP_REAL_DEFINED"
                            , "typedef mpq_srcptr SReal;"
                            , "#endif"
                            ]
         | True           = []

       rationalDecls
         | needsRational = [ "#ifndef SBV_GMP_RATIONAL_DEFINED"
                           , "#define SBV_GMP_RATIONAL_DEFINED"
                           , "typedef mpq_srcptr SRational;"
                           , "#endif"
                           ]
         | True          = []

-- | Emit the per-call arena and the exact numeric helpers required by a
-- program. Every temporary GMP value is released together at function exit.
gmpRuntime :: CgConfig -> Set.Set Kind -> [(SV, SBVExpr)] -> Doc
gmpRuntime cfg kinds assignments
  | not needsExactInteger && not needsExactQuotient = empty
  | True                                            = text . unlines . map markUnused $
      commonRuntime
   ++ [""]
   ++ concat [integerRuntime  | needsExactInteger]
   ++ concat [realRuntime     | needsExactQuotient]
   ++ concat [rationalRuntime cfg | needsRational]
   ++ concat [crossRuntime    | needsExactInteger && needsExactQuotient]
   ++ concatMap nativeGMPResultRuntime (nativeGMPResultKinds cfg assignments)
   ++ concat [concatMap wideIntegerRuntime conversions | needsExactInteger]
   ++ concat [concatMap wideQuotientRuntime quotientConversions | needsExactQuotient]
 where needsExactInteger   = isExactGMPKind cfg KUnbounded && KUnbounded `Set.member` kinds
       needsExactReal      = isExactGMPKind cfg KReal      && KReal      `Set.member` kinds
       needsRational       = KRational `Set.member` kinds
       needsExactQuotient  = needsExactReal || needsRational
       conversions         = nub (concatMap wideIntegerConversions assignments)
       quotientConversions = nub (concatMap wideQuotientConversions assignments)

       markUnused line = case stripPrefix "static " line of
                           Just rest -> "static SBV_CGEN_UNUSED " ++ rest
                           Nothing   -> line

-- | Render an exact integer, real, or rational constant as an arena allocation.
gmpConst :: CgConfig -> CV -> Maybe Doc
gmpConst cfg (CV KUnbounded (CInteger i))
  | isExactGMPKind cfg KUnbounded
  = Just $ namedCall "sbv_gmp_integer_const" [text "&__sbv_gmp_ctx", doubleQuotes (integer i)]
gmpConst cfg (CV KReal (CAlgReal (AlgRational _ r)))
  | isExactGMPKind cfg KReal
  = Just $ namedCall "sbv_gmp_real_const" [text "&__sbv_gmp_ctx", doubleQuotes (text value)]
  where value = show (numerator r) ++ "/" ++ show (denominator r)
gmpConst cfg (CV KReal (CAlgReal r))
  | isExactGMPKind cfg KReal
  = error $ "SBV->C: GMP-backed SReal constants must be rational, received " ++ show r
gmpConst _ (CV KRational (CRational r))
  = Just $ namedCall "sbv_gmp_real_const" [text "&__sbv_gmp_ctx", doubleQuotes (text value)]
  where value = show (numerator r) ++ "/" ++ show (denominator r)
gmpConst _ _ = Nothing

-- | Lower an operation involving an exact GMP value. A 'Nothing' result
-- delegates the operation to another C lowering module.
gmpExpr :: CgConfig -> Op -> [SV] -> Kind -> [Doc] -> Maybe CLowering
gmpExpr cfg op svs resultKind args
  | not (isExactGMPKind cfg resultKind || any (isExactGMPKind cfg . kindOf) svs)
  = Nothing
  | IEEEFP{} <- op
  = Nothing
  | KindCast fr to <- op
  , Just CgLongDouble <- cgReal cfg
  , KReal `elem` [fr, to]
  = error "SBV->C: Exact numeric conversions involving cgSRealType CgLongDouble are not yet supported; use CgFloat, CgDouble, or exact GMP reals."
  | KindCast fr to <- op
  , Just{} <- cgReal cfg
  , KReal `elem` [fr, to]
  = Nothing
  | LkUp{} <- op
  = Nothing
  | Uninterpreted functionName <- op
  , T.unpack functionName /= "sbv.rat.numerator"
  , T.unpack functionName /= "sbv.rat.denominator"
  = Nothing
  | True
  = case (op, args, svs) of
      (Label _              , [a]      , _)   -> lower a
      (Ite                  , [c, a, b], _)   -> lower $ c <+> text "?" <+> a <+> text ":" <+> b
      (Plus                 , [a, b]   , x:_) -> lower $ valueCall x "add" [a, b]
      (Minus                , [a, b]   , x:_) -> lower $ valueCall x "sub" [a, b]
      (Times                , [a, b]   , x:_) -> lower $ valueCall x "mul" [a, b]
      (NonLinear NR_IntPow  , [a, b]   , x:_) -> lower $ valueCall x "pow" [a, b]
      (UNeg                 , [a]      , x:_) -> lower $ valueCall x "neg" [a]
      (Abs                  , [a]      , x:_) -> lower $ valueCall x "abs" [a]
      (Quot                 , [a, b]   , x:_) -> lower $ valueCall x "quot" [a, b]
      (RationalConstructor  , [n, d]   , _)   -> lower $ namedCall "sbv_gmp_rational_construct" [text "&__sbv_gmp_ctx", n, d]
      (Uninterpreted funName, [a]      , _)
        | T.unpack funName == "sbv.rat.numerator"   -> lower $ namedCall "sbv_gmp_rational_numerator" [a]
        | T.unpack funName == "sbv.rat.denominator" -> lower $ namedCall "sbv_gmp_rational_denominator" [a]
      (Rem                  , [a, b]   , x:_)
        | kindOf x == KUnbounded                   -> lower $ valueCall x "rem" [a, b]
      (And                  , [a, b]   , x:_)
        | kindOf x == KUnbounded                   -> lower $ valueCall x "and" [a, b]
      (Or                   , [a, b]   , x:_)
        | kindOf x == KUnbounded                   -> lower $ valueCall x "or" [a, b]
      (XOr                  , [a, b]   , x:_)
        | kindOf x == KUnbounded                   -> lower $ valueCall x "xor" [a, b]
      (Not                  , [a]      , x:_)
        | kindOf x == KUnbounded                   -> lower $ valueCall x "com" [a]
      (Shl                  , [a, n]   , x:_)
        | kindOf x == KUnbounded                   -> lower $ valueCall x "shl" [a, n]
      (Shr                  , [a, n]   , x:_)
        | kindOf x == KUnbounded                   -> lower $ valueCall x "shr" [a, n]
      (Rol n                , [a]      , x:_)
        | kindOf x == KUnbounded                   -> lower $ valueCall x "shl" [a, integerValue n]
      (Ror n                , [a]      , x:_)
        | kindOf x == KUnbounded                   -> lower $ valueCall x "shr" [a, integerValue n]
      (Equal _              , [a, b]   , x:_) -> lower $ comparison x "==" a b
      (NotEqual             , as       , x:_) -> lower $ distinctExpr x as
      (LessThan             , [a, b]   , x:_) -> lower $ comparison x "<"  a b
      (GreaterThan          , [a, b]   , x:_) -> lower $ comparison x ">"  a b
      (LessEq               , [a, b]   , x:_) -> lower $ comparison x "<=" a b
      (GreaterEq            , [a, b]   , x:_) -> lower $ comparison x ">=" a b
      (Divides n            , [a]      , x:_)
        | kindOf x == KUnbounded                   -> lower $ namedCall "sbv_gmp_integer_divides"
                                                               [namedCall "sbv_gmp_integer_const" [text "&__sbv_gmp_ctx", doubleQuotes (integer n)], a]
      (KindCast fr to       , [a]      , _)   -> gmpCast fr to a
      _ -> unsupported
 where lower = lowerWith [CRequiresGMP]

       lowerWith requirements = Just . expressionLowering requirements

       valueCall sv suffix = namedCall (kindPrefix (kindOf sv) ++ suffix) . (text "&__sbv_gmp_ctx" :)

       comparison sv relation a b = parens $ namedCall (kindPrefix (kindOf sv) ++ "cmp") [a, b] <+> text relation <+> text "0"

       integerValue value = namedCall "sbv_gmp_integer_const" [text "&__sbv_gmp_ctx", doubleQuotes (integer (fromIntegral value))]

       distinctExpr sv as = fsep $ punctuate (text " &&")
                                  [parens (namedCall (kindPrefix (kindOf sv) ++ "cmp") [a, b] <+> text "!= 0")
                                  | (a:rest) <- tails as, b <- rest]

       gmpCast fr to a
         | fr == to = lower a
         | fr == KUnbounded && to `elem` [KReal, KRational]
         = if isExactGMPKind cfg KUnbounded
           then lower $ namedCall "sbv_gmp_real_from_integer" [text "&__sbv_gmp_ctx", a]
           else lower $ namedCall "sbv_gmp_real_from_s64"
                                  [text "&__sbv_gmp_ctx", parens (text "int64_t") <+> a]
         | fr == KReal && to == KUnbounded
         = if isExactGMPKind cfg to
           then lower $ namedCall "sbv_gmp_integer_from_real" [text "&__sbv_gmp_ctx", a]
           else lower $ nativeResult to (namedCall "sbv_gmp_real_low_u64" [a])
         | isWideBV fr && to `elem` [KReal, KRational]
         = lowerWith [CRequiresGMP, CRequiresWideBV] $ namedCall (quotientFromWideName fr) [text "&__sbv_gmp_ctx", a]
         | isWideBV fr && to == KUnbounded
         = lowerWith [CRequiresGMP, CRequiresWideBV] $ namedCall (integerFromWideName fr) [text "&__sbv_gmp_ctx", a]
         | fr == KUnbounded && isWideBV to
         = lowerWith [CRequiresGMP, CRequiresWideBV] $ namedCall (integerToWideName to) [a]
         | isBounded fr && intSizeOf fr <= 64 && to == KUnbounded
         = lower $ namedCall (if hasSign fr then "sbv_gmp_integer_from_s64" else "sbv_gmp_integer_from_u64")
                             [text "&__sbv_gmp_ctx", parens (text (if hasSign fr then "int64_t" else "uint64_t")) <+> a]
         | fr == KUnbounded && isBounded to && not (isWideBV to)
         = lower $ nativeResult to (namedCall "sbv_gmp_integer_low_u64" [a])
         | isBounded fr && intSizeOf fr <= 64 && to `elem` [KReal, KRational]
         = lower $ namedCall (if hasSign fr then "sbv_gmp_real_from_s64" else "sbv_gmp_real_from_u64")
                             [text "&__sbv_gmp_ctx", parens (text (if hasSign fr then "int64_t" else "uint64_t")) <+> a]
         | fr == KReal && isBounded to && not (isWideBV to)
         = lower $ nativeResult to (namedCall "sbv_gmp_real_low_u64" [a])
         | otherwise
         = unsupportedCast fr to

       nativeResult to value = namedCall (nativeGMPResultName (mappedIntegerKind (cgInteger cfg) to)) [value]

       unsupported = error $ "SBV->C: exact GMP lowering does not yet support " ++ show op
                          ++ " with argument kinds " ++ show (map kindOf svs)
                          ++ " and result kind " ++ show resultKind

       unsupportedCast fr to = error $ "SBV->C: exact GMP lowering does not yet support a cast from " ++ show fr ++ " to " ++ show to

-- | Discover native result representations for exact GMP casts. Explicitly
-- mapped integers use the same low-bit conversion as signed bit-vectors.
nativeGMPResultKinds :: CgConfig -> [(SV, SBVExpr)] -> [Kind]
nativeGMPResultKinds cfg = nub . concatMap resultKind
 where resultKind (_, SBVApp (KindCast fr to) _)
         | isExactGMPKind cfg fr
         , let target = mappedIntegerKind (cgInteger cfg) to
         , isBounded target
         , not (isWideBV target) = [target]
       resultKind _ = []

-- | Name a helper that interprets low integer bits in a native representation.
nativeGMPResultName :: Kind -> String
nativeGMPResultName kind = "sbv_gmp_low_bits_" ++ boundedTag kind

-- | Convert reduced unsigned bits without implementation-defined signed
-- narrowing or C's nonzero-to-Boolean conversion. A one-bit vector uses bit 0.
nativeGMPResultRuntime :: Kind -> [String]
nativeGMPResultRuntime kind =
  [ "static " ++ boundedCType kind ++ " " ++ nativeGMPResultName kind ++ "(uint64_t value)"
  , "{"
  ]
  ++ result
  ++ ["}", ""]
 where result
         | kind == KBounded False 1
         = ["  return (value & UINT64_C(1)) != 0;"]
         | hasSign kind
         = [ "  const SWord" ++ show (intSizeOf kind) ++ " bits = (SWord" ++ show (intSizeOf kind) ++ ") value;"
           , "  " ++ boundedCType kind ++ " result; memcpy(&result, &bits, sizeof result); return result;"
           ]
         | True
         = ["  return (" ++ boundedCType kind ++ ") value;"]

-- | A generated conversion between a limb-backed bit-vector and an exact GMP
-- integer.
data WideIntegerConversion = IntegerFromWide Kind
                           | IntegerToWide Kind
                           deriving Eq

-- | Discover wide bit-vector and exact-integer casts in one symbolic
-- assignment.
wideIntegerConversions :: (SV, SBVExpr) -> [WideIntegerConversion]
wideIntegerConversions (_, SBVApp (KindCast fr to) _)
  | isWideBV fr && to == KUnbounded = [IntegerFromWide fr]
  | fr == KUnbounded && isWideBV to = [IntegerToWide to]
wideIntegerConversions _ = []

-- | A generated conversion from a limb-backed bit-vector to an exact GMP
-- real or rational.
newtype WideQuotientConversion = QuotientFromWide Kind
                              deriving Eq

-- | Discover limb-backed bit-vector to exact real or rational casts in one
-- symbolic assignment.
wideQuotientConversions :: (SV, SBVExpr) -> [WideQuotientConversion]
wideQuotientConversions (_, SBVApp (KindCast fr to) _)
  | isWideBV fr
  , to `elem` [KReal, KRational] = [QuotientFromWide fr]
wideQuotientConversions _ = []

-- | Emit an exact conversion helper for one wide bit-vector kind.
wideIntegerRuntime :: WideIntegerConversion -> [String]
wideIntegerRuntime (IntegerFromWide k) =
  [ "static SInteger " ++ integerFromWideName k ++ "(sbv_gmp_ctx *ctx, " ++ boundedCType k ++ " a)"
  , "{"
  , "  mpz_ptr r = sbv_gmp_new_integer(ctx);"
  , "  mpz_import(r, " ++ show limbCount ++ ", -1, sizeof(a.limb[0]), 0, 0, a.limb);"
  ]
  ++ signedAdjustment
  ++ [ "  return r;"
     , "}"
     , ""
     ]
 where limbCount = (intSizeOf k + 63) `div` 64
       signedAdjustment
         | hasSign k =
             [ "  if ((a.limb[" ++ show topLimb ++ "] & " ++ u64 signMask ++ ") != 0) {"
             , "    mpz_t modulus; mpz_init_set_ui(modulus, 1); mpz_mul_2exp(modulus, modulus, " ++ show width ++ ");"
             , "    mpz_sub(r, r, modulus); mpz_clear(modulus);"
             , "  }"
             ]
         | True = []
       width    = intSizeOf k
       topLimb  = (width - 1) `div` 64
       signMask = 1 `shiftL` ((width - 1) `mod` 64)
wideIntegerRuntime (IntegerToWide k) =
  [ "static " ++ boundedCType k ++ " " ++ integerToWideName k ++ "(SInteger a)"
  , "{"
  , "  " ++ boundedCType k ++ " r = {{0}}; size_t count = 0; mpz_t reduced;"
  , "  mpz_init(reduced); mpz_fdiv_r_2exp(reduced, a, " ++ show (intSizeOf k) ++ ");"
  , "  mpz_export(r.limb, &count, -1, sizeof(r.limb[0]), 0, 0, reduced); mpz_clear(reduced);"
  , "  r.limb[" ++ show (limbCount - 1) ++ "] &= " ++ u64 topMask ++ ";"
  , "  return r;"
  , "}"
  , ""
  ]
 where limbCount = (intSizeOf k + 63) `div` 64
       remainder = intSizeOf k `mod` 64
       topMask
         | remainder == 0 = (1 `shiftL` 64) - 1
         | True           = (1 `shiftL` remainder) - 1

-- | Emit an exact real-or-rational conversion helper for one wide bit-vector
-- kind.
wideQuotientRuntime :: WideQuotientConversion -> [String]
wideQuotientRuntime (QuotientFromWide k) =
  [ "static mpq_srcptr " ++ quotientFromWideName k ++ "(sbv_gmp_ctx *ctx, " ++ boundedCType k ++ " a)"
  , "{"
  , "  mpq_ptr r = sbv_gmp_new_real(ctx);"
  , "  mpz_import(mpq_numref(r), " ++ show limbCount ++ ", -1, sizeof(a.limb[0]), 0, 0, a.limb);"
  ]
  ++ signedAdjustment
  ++ [ "  return r;"
     , "}"
     , ""
     ]
 where limbCount = (intSizeOf k + 63) `div` 64
       signedAdjustment
         | hasSign k =
             [ "  if ((a.limb[" ++ show topLimb ++ "] & " ++ u64 signMask ++ ") != 0) {"
             , "    mpz_t modulus; mpz_init_set_ui(modulus, 1); mpz_mul_2exp(modulus, modulus, " ++ show width ++ ");"
             , "    mpz_sub(mpq_numref(r), mpq_numref(r), modulus); mpz_clear(modulus);"
             , "  }"
             ]
         | True = []
       width    = intSizeOf k
       topLimb  = (width - 1) `div` 64
       signMask = 1 `shiftL` ((width - 1) `mod` 64)

-- | Construct the helper name for a wide bit-vector to exact-integer cast.
integerFromWideName :: Kind -> String
integerFromWideName k = "sbv_gmp_integer_from_" ++ boundedTag k

-- | Construct the helper name for an exact-integer to wide bit-vector cast.
integerToWideName :: Kind -> String
integerToWideName k = "sbv_gmp_integer_to_" ++ boundedTag k

-- | Construct the helper name for a wide bit-vector to an exact GMP quotient.
quotientFromWideName :: Kind -> String
quotientFromWideName k = "sbv_gmp_real_from_" ++ boundedTag k

-- | Return the C type used for a bounded SBV kind.
boundedCType :: Kind -> String
boundedCType (KBounded False 1) = "SBool"
boundedCType (KBounded False w) = "SWord" ++ show w
boundedCType (KBounded True  w) = "SInt"  ++ show w
boundedCType k                  = error $ "SBV->C: Expected a bounded kind, received " ++ show k

-- | Return the signedness-and-width suffix used in a conversion helper name.
boundedTag :: Kind -> String
boundedTag k
  | isBounded k = (if hasSign k then "s" else "u") ++ show (intSizeOf k)
  | True        = error $ "SBV->C: Expected a bounded kind, received " ++ show k

-- | Render a padded, portable C @uint64_t@ literal.
u64 :: Integer -> String
u64 value = "UINT64_C(0x" ++ replicate (16 - length rendered) '0' ++ rendered ++ ")"
 where rendered = showHex value ""

-- | Print an exact GMP value in canonical decimal notation.
gmpPrint :: Kind -> Doc -> Doc
gmpPrint KUnbounded value = namedCall "gmp_printf" [doubleQuotes (text "%Zd"), value]
gmpPrint KReal      value = namedCall "gmp_printf" [doubleQuotes (text "%Qd"), value]
gmpPrint KRational  value = namedCall "gmp_printf" [doubleQuotes (text "%Qd"), value]
gmpPrint k          _     = error $ "SBV->C: Expected an exact GMP kind, received " ++ show k

-- | Copy an internal immutable exact value into caller-owned GMP storage.
gmpSet :: Kind -> Doc -> Doc -> Doc
gmpSet KUnbounded target value = namedCall "mpz_set" [target, value]
gmpSet KReal      target value = namedCall "mpq_set" [target, value]
gmpSet KRational  target value = namedCall "mpq_set" [target, value]
gmpSet k          _      _     = error $ "SBV->C: Expected an exact GMP kind, received " ++ show k

-- | Return the mutable GMP pointer type used for an output parameter.
gmpOutputType :: Kind -> String
gmpOutputType KUnbounded = "mpz_ptr"
gmpOutputType KReal      = "mpq_ptr"
gmpOutputType KRational  = "mpq_ptr"
gmpOutputType k          = error $ "SBV->C: Expected an exact GMP kind, received " ++ show k

-- | Return the mutable GMP storage type used for one element of a generated
-- fixed-size array.
gmpArrayType :: Kind -> String
gmpArrayType KUnbounded = "mpz_t"
gmpArrayType KReal      = "mpq_t"
gmpArrayType KRational  = "mpq_t"
gmpArrayType kind       = error $ "SBV->C: Expected an exact GMP kind, received " ++ show kind

-- | Initialize already-declared caller-owned GMP storage from an
-- integer-valued driver sample.
gmpDriverInitialize :: Kind -> Doc -> Doc -> Doc
gmpDriverInitialize KUnbounded storage value = namedCall "mpz_init_set_str" [storage, doubleQuotes value, text "10"] P.<> semi
gmpDriverInitialize KReal      storage value = namedCall "mpq_init" [storage] P.<> semi
                                             $$ namedCall "mpq_set_str" [storage, doubleQuotes value, text "10"] P.<> semi
                                             $$ namedCall "mpq_canonicalize" [storage] P.<> semi
gmpDriverInitialize KRational  storage value = namedCall "mpq_init" [storage] P.<> semi
                                             $$ namedCall "mpq_set_str" [storage, doubleQuotes value, text "10"] P.<> semi
                                             $$ namedCall "mpq_canonicalize" [storage] P.<> semi
gmpDriverInitialize kind       _       _     = error $ "SBV->C: Expected an exact GMP kind, received " ++ show kind

-- | Declare and initialize a caller-owned GMP value from an integer-valued
-- driver sample.
gmpDriverInit :: Kind -> Doc -> Doc -> Doc
gmpDriverInit kind storage value = text (gmpArrayType kind) <+> storage P.<> semi
                                $$ gmpDriverInitialize kind storage value

-- | Clear caller-owned GMP storage in a generated driver.
gmpDriverClear :: Kind -> Doc -> Doc
gmpDriverClear KUnbounded storage = namedCall "mpz_clear" [storage] P.<> semi
gmpDriverClear KReal      storage = namedCall "mpq_clear" [storage] P.<> semi
gmpDriverClear KRational  storage = namedCall "mpq_clear" [storage] P.<> semi
gmpDriverClear k          _       = error $ "SBV->C: Expected an exact GMP kind, received " ++ show k

-- | Initialize the arena used by exact temporaries in a generated function.
gmpContextStart :: Doc
gmpContextStart = text "sbv_gmp_ctx __sbv_gmp_ctx = {NULL};"

-- | Release all exact temporaries allocated by a generated function.
gmpContextEnd :: Doc
gmpContextEnd = namedCall "sbv_gmp_ctx_end" [text "&__sbv_gmp_ctx"] P.<> semi

-- | Return the generated helper namespace for an exact numeric kind.
kindPrefix :: Kind -> String
kindPrefix KUnbounded = "sbv_gmp_integer_"
kindPrefix KReal      = "sbv_gmp_real_"
kindPrefix KRational  = "sbv_gmp_real_"
kindPrefix k          = error $ "SBV->C: Expected an exact GMP kind, received " ++ show k

-- | Render a C function call.
namedCall :: String -> [Doc] -> Doc
namedCall nm args = text nm P.<> parens (fsep (punctuate comma args))

-- | Runtime shared by exact integers, reals, and rationals.
commonRuntime :: [String]
commonRuntime =
  ["/* Per-call ownership arena for exact GMP temporaries. */"
  , "typedef struct sbv_gmp_node {"
  , "  struct sbv_gmp_node *next;"
  , "  bool is_real;"
  , "  union { mpz_t integer; mpq_t real; } value;"
  , "} sbv_gmp_node;"
  , ""
  , "typedef struct { sbv_gmp_node *head; } sbv_gmp_ctx;"
  , ""
  , "static mpz_ptr sbv_gmp_new_integer(sbv_gmp_ctx *ctx)"
  , "{"
  , "  sbv_gmp_node *node = (sbv_gmp_node *) malloc(sizeof(*node));"
  , "  if (node == NULL) abort();"
  , "  node->next = ctx->head; node->is_real = false; ctx->head = node;"
  , "  mpz_init(node->value.integer);"
  , "  return node->value.integer;"
  , "}"
  , ""
  , "static mpq_ptr sbv_gmp_new_real(sbv_gmp_ctx *ctx)"
  , "{"
  , "  sbv_gmp_node *node = (sbv_gmp_node *) malloc(sizeof(*node));"
  , "  if (node == NULL) abort();"
  , "  node->next = ctx->head; node->is_real = true; ctx->head = node;"
  , "  mpq_init(node->value.real);"
  , "  return node->value.real;"
  , "}"
  , ""
  , "static void sbv_gmp_ctx_end(sbv_gmp_ctx *ctx)"
  , "{"
  , "  while (ctx->head != NULL) {"
  , "    sbv_gmp_node *node = ctx->head; ctx->head = node->next;"
  , "    if (node->is_real) mpq_clear(node->value.real); else mpz_clear(node->value.integer);"
  , "    free(node);"
  , "  }"
  , "}"
  , ""
  , "static const void *sbv_gmp_ctx_retain_empty(const void *context)"
  , "{"
  , "  (void) context;"
  , "  sbv_gmp_ctx *owned = (sbv_gmp_ctx *) malloc(sizeof(*owned));"
  , "  if (owned == NULL) abort();"
  , "  owned->head = NULL;"
  , "  return owned;"
  , "}"
  , ""
  , "static void sbv_gmp_ctx_release_owned(const void *context)"
  , "{"
  , "  sbv_gmp_ctx *owned = (sbv_gmp_ctx *) context;"
  , "  sbv_gmp_ctx_end(owned);"
  , "  free(owned);"
  , "}"
  ]

-- | Runtime helpers for exact unbounded integers.
integerRuntime :: [String]
integerRuntime =
  ["static SInteger sbv_gmp_integer_const(sbv_gmp_ctx *ctx, const char *value)"
  , "{ mpz_ptr r = sbv_gmp_new_integer(ctx); if (mpz_set_str(r, value, 10) != 0) abort(); return r; }"
  , ""
  , "static SInteger sbv_gmp_integer_from_u64(sbv_gmp_ctx *ctx, uint64_t value)"
  , "{ mpz_ptr r = sbv_gmp_new_integer(ctx); mpz_import(r, 1, -1, sizeof(value), 0, 0, &value); return r; }"
  , ""
  , "static SInteger sbv_gmp_integer_from_s64(sbv_gmp_ctx *ctx, int64_t value)"
  , "{"
  , "  const uint64_t magnitude = value < 0 ? UINT64_C(0) - (uint64_t) value : (uint64_t) value;"
  , "  mpz_ptr r = sbv_gmp_new_integer(ctx); mpz_import(r, 1, -1, sizeof(magnitude), 0, 0, &magnitude);"
  , "  if (value < 0) mpz_neg(r, r); return r;"
  , "}"
  , ""
  , "static uint64_t sbv_gmp_integer_low_u64(SInteger value)"
  , "{"
  , "  uint64_t result = 0; size_t count; mpz_t reduced;"
  , "  mpz_init(reduced); mpz_fdiv_r_2exp(reduced, value, 64);"
  , "  mpz_export(&result, &count, -1, sizeof(result), 0, 0, reduced); mpz_clear(reduced); return result;"
  , "}"
  , ""
  ]
  ++ concatMap integerUnary [("neg", "mpz_neg"), ("abs", "mpz_abs"), ("com", "mpz_com")]
  ++ concatMap integerBinary [("add", "mpz_add"), ("sub", "mpz_sub"), ("mul", "mpz_mul"), ("and", "mpz_and"), ("or", "mpz_ior"), ("xor", "mpz_xor")]
  ++ ["static SInteger sbv_gmp_integer_quot(sbv_gmp_ctx *ctx, SInteger a, SInteger b)"
     , "{"
     , "  mpz_ptr r = sbv_gmp_new_integer(ctx); mpz_t divisor;"
     , "  if (mpz_sgn(b) == 0) { mpz_set(r, a); return r; }"
     , "  mpz_init(divisor); mpz_abs(divisor, b); mpz_fdiv_q(r, a, divisor);"
     , "  if (mpz_sgn(b) < 0) mpz_neg(r, r); mpz_clear(divisor); return r;"
     , "}"
     , ""
     , "static SInteger sbv_gmp_integer_rem(sbv_gmp_ctx *ctx, SInteger a, SInteger b)"
     , "{"
     , "  mpz_ptr r = sbv_gmp_new_integer(ctx); mpz_t divisor;"
     , "  if (mpz_sgn(b) == 0) { mpz_set(r, a); return r; }"
     , "  mpz_init(divisor); mpz_abs(divisor, b); mpz_fdiv_r(r, a, divisor); mpz_clear(divisor); return r;"
     , "}"
     , ""
     , "static int sbv_gmp_integer_cmp(SInteger a, SInteger b) { return mpz_cmp(a, b); }"
     , ""
     , "static bool sbv_gmp_integer_divides(SInteger divisor, SInteger value)"
     , "{ return mpz_sgn(divisor) != 0 && mpz_divisible_p(value, divisor) != 0; }"
     , ""
     , "static SInteger sbv_gmp_integer_pow(sbv_gmp_ctx *ctx, SInteger base, SInteger exponent)"
     , "{"
     , "  mpz_ptr result = sbv_gmp_new_integer(ctx); mpz_t factor, power;"
     , "  if (mpz_sgn(exponent) < 0) {"
     , "    if (mpz_cmp_si(base, 1) == 0) mpz_set_ui(result, 1);"
     , "    else if (mpz_cmp_si(base, -1) == 0) mpz_set_si(result, mpz_odd_p(exponent) ? -1 : 1);"
     , "    else mpz_set_ui(result, 0);"
     , "    return result;"
     , "  }"
     , "  mpz_set_ui(result, 1); mpz_init_set(factor, base); mpz_init_set(power, exponent);"
     , "  while (mpz_sgn(power) != 0) {"
     , "    if (mpz_odd_p(power)) mpz_mul(result, result, factor);"
     , "    mpz_fdiv_q_2exp(power, power, 1);"
     , "    if (mpz_sgn(power) != 0) mpz_mul(factor, factor, factor);"
     , "  }"
     , "  mpz_clear(power); mpz_clear(factor); return result;"
     , "}"
     , ""
     , "static SInteger sbv_gmp_integer_shift(sbv_gmp_ctx *ctx, SInteger a, SInteger amount, bool left)"
     , "{"
     , "  mpz_ptr r = sbv_gmp_new_integer(ctx); mpz_t magnitude; bool effective_left = left;"
     , "  mpz_init(magnitude); mpz_abs(magnitude, amount);"
     , "  if (mpz_sgn(amount) < 0) effective_left = !effective_left;"
     , "  if (!mpz_fits_ulong_p(magnitude)) {"
     , "    if (effective_left) abort();"
     , "    mpz_set_si(r, mpz_sgn(a) < 0 ? -1 : 0);"
     , "  } else if (effective_left) {"
     , "    mpz_mul_2exp(r, a, mpz_get_ui(magnitude));"
     , "  } else {"
     , "    mpz_fdiv_q_2exp(r, a, mpz_get_ui(magnitude));"
     , "  }"
     , "  mpz_clear(magnitude); return r;"
     , "}"
     , ""
     , "static SInteger sbv_gmp_integer_shl(sbv_gmp_ctx *ctx, SInteger a, SInteger amount)"
     , "{ return sbv_gmp_integer_shift(ctx, a, amount, true); }"
     , ""
     , "static SInteger sbv_gmp_integer_shr(sbv_gmp_ctx *ctx, SInteger a, SInteger amount)"
     , "{ return sbv_gmp_integer_shift(ctx, a, amount, false); }"
     , ""
     ]
 where integerUnary (suffix, operation) =
         ["static SInteger sbv_gmp_integer_" ++ suffix ++ "(sbv_gmp_ctx *ctx, SInteger a)"
         , "{ mpz_ptr r = sbv_gmp_new_integer(ctx); " ++ operation ++ "(r, a); return r; }"
         , ""]

       integerBinary (suffix, operation) =
         ["static SInteger sbv_gmp_integer_" ++ suffix ++ "(sbv_gmp_ctx *ctx, SInteger a, SInteger b)"
         , "{ mpz_ptr r = sbv_gmp_new_integer(ctx); " ++ operation ++ "(r, a, b); return r; }"
         , ""]

-- | Runtime helpers shared by exact reals and symbolic rationals.
realRuntime :: [String]
realRuntime =
  ["static mpq_srcptr sbv_gmp_real_const(sbv_gmp_ctx *ctx, const char *value)"
  , "{ mpq_ptr r = sbv_gmp_new_real(ctx); if (mpq_set_str(r, value, 10) != 0) abort(); mpq_canonicalize(r); return r; }"
  , ""
  , "static mpq_srcptr sbv_gmp_real_from_u64(sbv_gmp_ctx *ctx, uint64_t value)"
  , "{ mpq_ptr r = sbv_gmp_new_real(ctx); mpz_import(mpq_numref(r), 1, -1, sizeof(value), 0, 0, &value); return r; }"
  , ""
  , "static mpq_srcptr sbv_gmp_real_from_s64(sbv_gmp_ctx *ctx, int64_t value)"
  , "{"
  , "  const uint64_t magnitude = value < 0 ? UINT64_C(0) - (uint64_t) value : (uint64_t) value;"
  , "  mpq_ptr r = sbv_gmp_new_real(ctx); mpz_import(mpq_numref(r), 1, -1, sizeof(magnitude), 0, 0, &magnitude);"
  , "  if (value < 0) mpz_neg(mpq_numref(r), mpq_numref(r)); return r;"
  , "}"
  , ""
  , "static uint64_t sbv_gmp_real_low_u64(mpq_srcptr value)"
  , "{"
  , "  uint64_t result = 0; size_t count; mpz_t rounded, reduced;"
  , "  mpz_init(rounded); mpz_init(reduced); mpz_fdiv_q(rounded, mpq_numref(value), mpq_denref(value));"
  , "  mpz_fdiv_r_2exp(reduced, rounded, 64); mpz_export(&result, &count, -1, sizeof(result), 0, 0, reduced);"
  , "  mpz_clear(reduced); mpz_clear(rounded); return result;"
  , "}"
  , ""
  ]
  ++ concatMap realUnary [("neg", "mpq_neg"), ("abs", "mpq_abs")]
  ++ concatMap realBinary [("add", "mpq_add"), ("sub", "mpq_sub"), ("mul", "mpq_mul")]
  ++ ["static mpq_srcptr sbv_gmp_real_quot(sbv_gmp_ctx *ctx, mpq_srcptr a, mpq_srcptr b)"
     , "{ mpq_ptr r = sbv_gmp_new_real(ctx); if (mpq_sgn(b) == 0) mpq_set_ui(r, 0, 1); else mpq_div(r, a, b); return r; }"
     , ""
     , "static int sbv_gmp_real_cmp(mpq_srcptr a, mpq_srcptr b) { return mpq_cmp(a, b); }"
     , ""
     ]
 where realUnary (suffix, operation) =
         ["static mpq_srcptr sbv_gmp_real_" ++ suffix ++ "(sbv_gmp_ctx *ctx, mpq_srcptr a)"
         , "{ mpq_ptr r = sbv_gmp_new_real(ctx); " ++ operation ++ "(r, a); return r; }"
         , ""]

       realBinary (suffix, operation) =
         ["static mpq_srcptr sbv_gmp_real_" ++ suffix ++ "(sbv_gmp_ctx *ctx, mpq_srcptr a, mpq_srcptr b)"
         , "{ mpq_ptr r = sbv_gmp_new_real(ctx); " ++ operation ++ "(r, a, b); return r; }"
         , ""]

-- | Runtime helpers for the symbolic-rational constructor and internal
-- numerator/denominator accessors.
rationalRuntime :: CgConfig -> [String]
rationalRuntime cfg
  | isExactGMPKind cfg KUnbounded = exactRuntime
  | Just width <- cgInteger cfg   = mappedRuntime width
  | True                          = error "SBV->C: Cannot determine the SInteger representation used by SRational."
 where exactRuntime =
        ["static SRational sbv_gmp_rational_construct(sbv_gmp_ctx *ctx, mpz_srcptr numerator, mpz_srcptr denominator)"
        , "{"
        , "  mpq_ptr r = sbv_gmp_new_real(ctx);"
        , "  if (mpz_sgn(denominator) == 0) { mpq_set_ui(r, 0, 1); return r; }"
        , "  mpz_set(mpq_numref(r), numerator); mpz_set(mpq_denref(r), denominator);"
        , "  if (mpz_sgn(mpq_denref(r)) < 0) { mpz_neg(mpq_numref(r), mpq_numref(r)); mpz_neg(mpq_denref(r), mpq_denref(r)); }"
        , "  mpq_canonicalize(r); return r;"
        , "}"
        , ""
        , "static mpz_srcptr sbv_gmp_rational_numerator(SRational value) { return mpq_numref(value); }"
        , ""
        , "static mpz_srcptr sbv_gmp_rational_denominator(SRational value) { return mpq_denref(value); }"
        , ""
        ]

       mappedRuntime width =
        ["static void sbv_gmp_rational_set_s64(mpz_ptr target, int64_t value)"
        , "{"
        , "  const uint64_t magnitude = value < 0 ? UINT64_C(0) - (uint64_t) value : (uint64_t) value;"
        , "  mpz_import(target, 1, -1, sizeof(magnitude), 0, 0, &magnitude);"
        , "  if (value < 0) mpz_neg(target, target);"
        , "}"
        , ""
        , "static SInteger sbv_gmp_rational_part(mpz_srcptr value)"
        , "{"
        , "  " ++ unsignedType width ++ " bits = 0; size_t count; mpz_t reduced; SInteger result;"
        , "  mpz_init(reduced); mpz_fdiv_r_2exp(reduced, value, " ++ show width ++ ");"
        , "  mpz_export(&bits, &count, -1, sizeof(bits), 0, 0, reduced); mpz_clear(reduced);"
        , "  memcpy(&result, &bits, sizeof result); return result;"
        , "}"
        , ""
        , "static SRational sbv_gmp_rational_construct(sbv_gmp_ctx *ctx, SInteger numerator, SInteger denominator)"
        , "{"
        , "  mpq_ptr r = sbv_gmp_new_real(ctx);"
        , "  if (denominator == 0) { mpq_set_ui(r, 0, 1); return r; }"
        , "  sbv_gmp_rational_set_s64(mpq_numref(r), (int64_t) numerator);"
        , "  sbv_gmp_rational_set_s64(mpq_denref(r), (int64_t) denominator);"
        , "  if (mpz_sgn(mpq_denref(r)) < 0) { mpz_neg(mpq_numref(r), mpq_numref(r)); mpz_neg(mpq_denref(r), mpq_denref(r)); }"
        , "  mpq_canonicalize(r); return r;"
        , "}"
        , ""
        , "static SInteger sbv_gmp_rational_numerator(SRational value) { return sbv_gmp_rational_part(mpq_numref(value)); }"
        , ""
        , "static SInteger sbv_gmp_rational_denominator(SRational value) { return sbv_gmp_rational_part(mpq_denref(value)); }"
        , ""
        ]

       unsignedType width = "SWord" ++ show width

-- | Runtime helpers that convert between exact integers and GMP quotients.
crossRuntime :: [String]
crossRuntime =
  ["static SInteger sbv_gmp_integer_from_real(sbv_gmp_ctx *ctx, mpq_srcptr a)"
  , "{ mpz_ptr r = sbv_gmp_new_integer(ctx); mpz_fdiv_q(r, mpq_numref(a), mpq_denref(a)); return r; }"
  , ""
  , "static mpq_srcptr sbv_gmp_real_from_integer(sbv_gmp_ctx *ctx, SInteger a)"
  , "{ mpq_ptr r = sbv_gmp_new_real(ctx); mpq_set_z(r, a); return r; }"
  , ""
  ]
