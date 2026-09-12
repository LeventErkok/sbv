-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.FP
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- LibBF-backed lowering of arbitrary IEEE-754 floating-point values to C.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.FP
  ( arbitraryFPKinds
  , roundingModeTypeDecls
  , roundingModeConst
  , roundingModeDriverValue
  , arbitraryFPTypeDecls
  , arbitraryFPRuntime
  , arbitraryFPConst
  , arbitraryFPExpr
  , nativeFPRuntime
  , nativeFPExpr
  , nativeFPCompilePragmas
  , arbitraryFPNormalize
  , arbitraryFPPrint
  , arbitraryFPCType
  , arbitraryFPEqual
  , arbitraryFPObjectEqual
  , arbitraryFPIsNaN
  , nativeFPObjectEqual
  ) where

import Data.Bits                       (shiftL, shiftR, (.&.))
import Data.List                       (intercalate, nub, tails)
import qualified Data.Set as Set
import Numeric                         (showHex)

import qualified LibBF as BF

import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as P ((<>))

import Data.SBV.Compilers.C.BV        (isWideBV, mappedIntegerKind)
import Data.SBV.Compilers.C.GMP       (isExactGMPKind)
import Data.SBV.Compilers.C.Lowering  (CLowering, CRequirement(..), expressionLowering)
import Data.SBV.Compilers.CodeGen      (CgConfig(..), CgSRealType(..))
import Data.SBV.Core.Data
import Data.SBV.Core.SizedFloats       (FP(..), mkBFOpts)

-- | Disable implicit contraction in generated translation units without
-- changing the caller's compilation state through a public header. The
-- Makefiles also pass @-ffp-contract=off@: Clang can ignore these pragmas when
-- contraction is explicitly enabled on the command line. Explicit FMA calls
-- retain their single-rounding semantics.
nativeFPCompilePragmas :: Doc
nativeFPCompilePragmas = text . unlines $
  ["/* Preserve separate SBV rounding steps; explicit fma calls remain fused. */"
  , "#if defined(__GNUC__) && !defined(__clang__)"
  , "#pragma GCC optimize (\"fp-contract=off\")"
  , "#else"
  , "#pragma STDC FP_CONTRACT OFF"
  , "#endif"
  , ""]

-- | The distinct arbitrary floating-point kinds used by a program.
arbitraryFPKinds :: Set.Set Kind -> [Kind]
arbitraryFPKinds = map validate . filter isFP . Set.toAscList
 where validate k@(KFP eb _)
         | eb <= 61 = k
         | True     = error $ "SBV->C: LibBF supports arbitrary floating-point exponent widths only up to 61 bits, received " ++ show k
       validate k = error $ "SBV->C: Expected an arbitrary floating-point kind, received " ++ show k

-- | Declare the public C enumeration used for symbolic rounding modes.
roundingModeTypeDecls :: Bool -> Doc
roundingModeTypeDecls required
  | required = text . unlines $
      ["/* IEEE-754 rounding modes. */"
      , "#ifndef SBV_ROUNDING_MODE_DEFINED"
      , "#define SBV_ROUNDING_MODE_DEFINED"
      , "typedef enum { SBV_RM_RNE = 0, SBV_RM_RNA = 1, SBV_RM_RTP = 2, SBV_RM_RTN = 3, SBV_RM_RTZ = 4 } RoundingMode;"
      , "#endif"
      , ""]
  | True     = empty

-- | Render an SBV rounding-mode constant as a public C enumerator.
roundingModeConst :: CV -> Maybe Doc
roundingModeConst (CV k (CADT (constructorName, [])))
  | isRoundingMode k = text . fst <$> lookup constructorName roundingModeNames
roundingModeConst _ = Nothing

-- | Select a deterministic rounding-mode enumerator for a generated driver.
roundingModeDriverValue :: Integer -> Doc
roundingModeDriverValue sample = text cName
 where (cName, _) = map snd roundingModeNames !! fromInteger (sample `mod` toInteger (length roundingModeNames))

-- | Declare the raw IEEE interchange representation used at the public C ABI.
arbitraryFPTypeDecls :: [Kind] -> Doc
arbitraryFPTypeDecls [] = empty
arbitraryFPTypeDecls ks = text . unlines $
     ["/* Arbitrary IEEE-754 values, encoded as raw interchange bits. */"
     , "#ifndef SBV_CGEN_UNUSED"
     , "#if defined(__GNUC__) || defined(__clang__)"
     , "#define SBV_CGEN_UNUSED __attribute__((unused))"
     , "#else"
     , "#define SBV_CGEN_UNUSED"
     , "#endif"
     , "#endif"]
  ++ concatMap decl ks
 where decl k = ["#ifndef " ++ typeGuard k
                , "#define " ++ typeGuard k
                , "typedef struct { uint64_t limb[" ++ show (limbs k) ++ "]; } " ++ arbitraryFPCType k ++ ";"
                , "static inline SBV_CGEN_UNUSED void " ++ prefix k ++ "_fprint(FILE *stream, " ++ arbitraryFPCType k ++ " value)"
                , "{"
                , "  size_t i = " ++ show (limbs k) ++ ";"
                , "  fputs(\"0x\", stream);"
                , "  while (i-- > 0) fprintf(stream, \"%016\" PRIx64, value.limb[i]);"
                , "}"
                , "#endif"
                , ""]

       typeGuard (KFP eb sb) = "SBV_FP_E" ++ show eb ++ "_S" ++ show sb ++ "_DEFINED"
       typeGuard k           = error $ "SBV->C: Expected an arbitrary floating-point kind, received " ++ show k

-- | Emit the LibBF adapter and helpers for arbitrary formats and conversions
-- that require exact rounding.
arbitraryFPRuntime :: CgConfig -> [Kind] -> [(SV, SBVExpr)] -> Doc
arbitraryFPRuntime cfg ks asgns
  | null ks && null floatCasts = empty
  | True                       = text . unlines . map markUnused $
     ["/* LibBF-backed arbitrary floating-point runtime. */"
     , "#ifndef SBV_CGEN_UNUSED"
     , "#if defined(__GNUC__) || defined(__clang__)"
     , "#define SBV_CGEN_UNUSED __attribute__((unused))"
     , "#else"
     , "#define SBV_CGEN_UNUSED"
     , "#endif"
     , "#endif"
     , ""
     , "static inline bf_rnd_t sbv_bf_rounding_mode(int mode)"
     , "{"
     , "  switch (mode) {"
     , "    case 0: return BF_RNDN;"
     , "    case 1: return BF_RNDNA;"
     , "    case 2: return BF_RNDU;"
     , "    case 3: return BF_RNDD;"
     , "    case 4: return BF_RNDZ;"
     , "    default: abort();"
     , "  }"
     , "}"
     , ""
     , "static void *sbv_bf_realloc(void *opaque, void *ptr, size_t size)"
     , "{"
     , "  (void) opaque;"
     , "  return realloc(ptr, size);"
     , "}"
     , ""]
  ++ concatMap formatRuntime ks
  ++ concat [exactBridgeRuntime | any castUsesExact floatCasts]
  ++ concatMap reinterpretRuntime (nub (concatMap reinterprets asgns))
  ++ concatMap (castRuntime cfg) floatCasts
 where markUnused line = case splitAt 7 line of
                           ("static ", rest) -> "static SBV_CGEN_UNUSED " ++ rest
                           _                 -> line

       reinterprets (_, SBVApp (IEEEFP (FP_Reinterpret fr to)) _)
         | isFP fr || isFP to = [Reinterpret fr to]
       reinterprets _ = []

       casts (_, SBVApp (IEEEFP (FP_Cast fr to _)) _)
         | supportedCast fr to
         , not (exactNativeFPCast (floatCastKind cfg fr) (floatCastKind cfg to)) = [FloatCast fr to]
       casts (_, SBVApp (KindCast fr to) _)
         | mappedFloatCast cfg fr to = [FloatCast fr to]
       casts _ = []

       floatCasts = nub (concatMap casts asgns)

       castUsesExact (FloatCast fr to) = isExactGMPKind cfg fr || isExactGMPKind cfg to

       exactNativeCast fr to = (isExactGMPKind cfg fr && isNativeFloat to)
                            || (isNativeFloat fr && isExactGMPKind cfg to)

       nativeBitVectorCast fr to = (isBounded fr && isNativeFloat to)
                                || (isNativeFloat fr && isBounded to)

       nativeFloatCast fr to = isNativeFloat fr && isNativeFloat to

       supportedCast fr to = isFP fr
                          || isFP to
                          || mappedFloatCast cfg fr to
                          || exactNativeCast fr to
                          || nativeBitVectorCast fr to
                          || nativeFloatCast fr to

       isNativeFloat k = k == KFloat || k == KDouble

-- | Render an arbitrary floating-point constant in raw interchange form.
arbitraryFPConst :: Kind -> FP -> Maybe Doc
arbitraryFPConst k@(KFP eb sb) (FP _ _ value) = Just . text $ rawLiteral k bits
 where bits = BF.bfToBits (mkBFOpts eb sb BF.NearEven) value
arbitraryFPConst _ _ = Nothing

-- | Lower an operation requiring LibBF-backed floating-point semantics. A
-- 'Nothing' result delegates native RNE operations, table lookup, and
-- user-defined functions to the general C renderer.
-- Numeric floating casts use the bridge unless their native conversion is
-- provably exact: C casts and @rint@ would otherwise depend on the caller's
-- hardware rounding mode, even for RNE.
arbitraryFPExpr :: CgConfig -> [(SV, CV)] -> Op -> [SV] -> Kind -> [Doc] -> Maybe CLowering
arbitraryFPExpr cfg consts op svs resultKind args
  | IEEEFP (FP_Cast fr to rm) <- op
  , let target = floatCastKind cfg to
  , exactNativeFPCast (floatCastKind cfg fr) target
  , value:_ <- reverse args
  , let ignored = maybe [text (show rm)] (const []) (lookup rm consts)
  , let cast = parens (text (if isFloat target then "SFloat" else "SDouble")) <+> value
  = Just . expressionLowering [] $ case ignored of
      [] -> cast
      _  -> parens $ fsep (punctuate comma (map (text "(void)" <+>) ignored ++ [cast]))
  | not (isFP resultKind
      || any (isFP . kindOf) svs
      || isExactNativeCast
      || isNativeBitVectorCast
      || isNativeFloatCast
      || isMappedCast)
  = Nothing
  | LkUp{} <- op
  = Nothing
  | Uninterpreted{} <- op
  = Nothing
  | True
  = Just . expressionLowering requirements $ case (op, args, svs) of
      (Label _         , [a]         , _)            -> a
      (Ite             , [c, a, b]   , _)            -> c <+> text "?" <+> a <+> text ":" <+> b
      (UNeg            , [a]         , x:_)          -> argCall x "neg" [a]
      (Abs             , [a]         , x:_)          -> argCall x "abs" [a]
      (Plus            , [a, b]      , x:_)          -> argCall x "add" [a, b, text "BF_RNDN"]
      (Minus           , [a, b]      , x:_)          -> argCall x "sub" [a, b, text "BF_RNDN"]
      (Times           , [a, b]      , x:_)          -> argCall x "mul" [a, b, text "BF_RNDN"]
      (Equal False     , [a, b]      , x:_)          -> argCall x "eq" [a, b]
      (Equal True      , [a, b]      , x:_)          -> argCall x "obj_eq" [a, b]
      (NotEqual        , as          , x:_)          -> distinctExpr x as
      (LessThan        , [a, b]      , x:_)          -> argCall x "lt" [a, b]
      (GreaterThan     , [a, b]      , x:_)          -> argCall x "lt" [b, a]
      (LessEq          , [a, b]      , x:_)          -> argCall x "le" [a, b]
      (GreaterEq       , [a, b]      , x:_)          -> argCall x "le" [b, a]
      (IEEEFP fpOp     , as          , fpArgs)       -> fpExpr fpOp as fpArgs
      (KindCast fr to  , [a]         , _)            -> namedCall (castName fr to)
                                                         ([text "&__sbv_gmp_ctx" | isExactGMPKind cfg to]
                                                       ++ [a, text (if fr == KReal && to == KUnbounded then "BF_RNDD" else "BF_RNDN")])
      _                                              -> unsupported
 where argCall sv suffix = namedCall (prefix (kindOf sv) ++ "_" ++ suffix)

       distinctExpr sv as = fsep $ punctuate (text " &&")
                                  [text "!" P.<> parens (argCall sv "eq" [a, b])
                                  | (a:rest) <- tails as, b <- rest]

       fpExpr fpOp as fpArgs = case (fpOp, as, fpArgs) of
         (FP_Abs              , [a]           , x:_)    -> argCall x "abs" [a]
         (FP_Neg              , [a]           , x:_)    -> argCall x "neg" [a]
         (FP_Add              , [_rm, a, b]   , r:x:_)  -> argCall x "add" [a, b, bfRoundingMode consts r]
         (FP_Sub              , [_rm, a, b]   , r:x:_)  -> argCall x "sub" [a, b, bfRoundingMode consts r]
         (FP_Mul              , [_rm, a, b]   , r:x:_)  -> argCall x "mul" [a, b, bfRoundingMode consts r]
         (FP_Div              , [_rm, a, b]   , r:x:_)  -> argCall x "div" [a, b, bfRoundingMode consts r]
         (FP_FMA              , [_rm, a, b, c], r:x:_)  -> argCall x "fma" [a, b, c, bfRoundingMode consts r]
         (FP_Sqrt             , [_rm, a]      , r:x:_)  -> argCall x "sqrt" [a, bfRoundingMode consts r]
         (FP_Rem              , [a, b]        , x:_)    -> argCall x "rem" [a, b]
         (FP_RoundToIntegral  , [_rm, a]      , r:x:_)  -> argCall x "round" [a, bfRoundingMode consts r]
         (FP_Min              , [a, b]        , x:_)    -> argCall x "min" [a, b]
         (FP_Max              , [a, b]        , x:_)    -> argCall x "max" [a, b]
         (FP_ObjEqual         , [a, b]        , x:_)    -> argCall x "obj_eq" [a, b]
         (FP_IsNormal         , [a]           , x:_)    -> argCall x "is_normal" [a]
         (FP_IsSubnormal      , [a]           , x:_)    -> argCall x "is_subnormal" [a]
         (FP_IsZero           , [a]           , x:_)    -> argCall x "is_zero" [a]
         (FP_IsInfinite       , [a]           , x:_)    -> argCall x "is_infinite" [a]
         (FP_IsNaN            , [a]           , x:_)    -> argCall x "is_nan" [a]
         (FP_IsNegative       , [a]           , x:_)    -> argCall x "is_negative" [a]
         (FP_IsPositive       , [a]           , x:_)    -> argCall x "is_positive" [a]
         (FP_Reinterpret fr to, [a]           , _)      -> namedCall (reinterpretName fr to) [a]
         (FP_Cast fr to rm    , [a]           , _)      -> namedCall (castName fr to) (castArgs to a rm)
         (FP_Cast fr to rm    , [_rm, a]      , _)      -> namedCall (castName fr to) (castArgs to a rm)
         _                                              -> unsupported

       castArgs to a rm
         | isExactGMPKind cfg to = [text "&__sbv_gmp_ctx", a, bfRoundingMode consts rm]
         | True                  = [a, bfRoundingMode consts rm]

       requirements = [CRequiresLibBF, CRequiresLibM] ++ [CRequiresGMP | usesExact]

       usesExact = isExactGMPKind cfg resultKind || any (isExactGMPKind cfg . kindOf) svs

       isExactNativeCast = case op of
         IEEEFP (FP_Cast fr to _) -> (isExactGMPKind cfg fr && isNativeFloat to)
                                  || (isNativeFloat fr && isExactGMPKind cfg to)
         _                         -> False

       isNativeBitVectorCast = case op of
         IEEEFP (FP_Cast fr to _) -> (isBounded fr     && isNativeFloat to)
                                  || (isNativeFloat fr && isBounded to)
         _                         -> False

       isNativeFloatCast = case op of
         IEEEFP (FP_Cast fr to _) -> isNativeFloat fr && isNativeFloat to
         _                         -> False

       isMappedCast = case op of
         IEEEFP (FP_Cast fr to _) -> mappedFloatCast cfg fr to
         KindCast fr to          -> mappedFloatCast cfg fr to
         _                        -> False

       isNativeFloat k = k == KFloat || k == KDouble

       unsupported = error $ "SBV->C: arbitrary floating-point lowering does not yet support " ++ show op
                          ++ " with argument kinds " ++ show (map kindOf svs)
                          ++ " and result kind " ++ show resultKind

-- | Identify scalar casts whose entire source range is exactly representable
-- in the destination. No rounding, software adapter, or hardware rounding-mode
-- change is needed for any valid SBV rounding mode.
exactNativeFPCast :: Kind -> Kind -> Bool
exactNativeFPCast from to
  | to `notElem` [KFloat, KDouble] = False
  | from == to                   = True
  | from == KFloat, to == KDouble = True
  | isBounded from
  , not (isWideBV from)           = intSizeOf from - (if hasSign from then 1 else 0) <= significandBits to
  | True                         = False

-- | Emit LibBF adapters for native 'SFloat' and 'SDouble' operations whose
-- rounding mode cannot safely be expressed as an ordinary C expression.
nativeFPRuntime :: Doc
nativeFPRuntime = text . unlines . map markUnused $
     ["/* Exact rounding adapters for native floating-point operations. */"
     , "#ifndef SBV_CGEN_UNUSED"
     , "#if defined(__GNUC__) || defined(__clang__)"
     , "#define SBV_CGEN_UNUSED __attribute__((unused))"
     , "#else"
     , "#define SBV_CGEN_UNUSED"
     , "#endif"
     , "#endif"
     , ""
     , "static inline bf_rnd_t sbv_native_bf_rounding_mode(int mode)"
     , "{"
     , "  switch (mode) {"
     , "    case 0: return BF_RNDN;"
     , "    case 1: return BF_RNDNA;"
     , "    case 2: return BF_RNDU;"
     , "    case 3: return BF_RNDD;"
     , "    case 4: return BF_RNDZ;"
     , "    default: abort();"
     , "  }"
     , "}"
     , ""
     , "static void *sbv_native_bf_realloc(void *opaque, void *ptr, size_t size)"
     , "{"
     , "  (void) opaque;"
     , "  return realloc(ptr, size);"
     , "}"
     , ""
     ]
  ++ concatMap format [("SFloat", "float", 24, 8), ("SDouble", "double", 53, 11)]
 where markUnused line = case splitAt 14 line of
                           ("static inline ", rest) -> "static inline SBV_CGEN_UNUSED " ++ rest
                           _                        -> line

       format :: (String, String, Int, Int) -> [String]
       format (cType, tag, precision, exponentBits) =
            ["static inline bf_flags_t sbv_native_" ++ tag ++ "_flags(bf_rnd_t rnd)"
            , "{ return (bf_flags_t) rnd | BF_FLAG_SUBNORMAL | bf_set_exp_bits(" ++ show exponentBits ++ "); }"
            , ""
            , "static inline " ++ cType ++ " sbv_native_" ++ tag ++ "_finish(bf_t *value, bf_rnd_t rnd)"
            , "{"
            , "  double result;"
            , "  bf_get_float64(value, &result, rnd);"
            , "  return (" ++ cType ++ ") result;"
            , "}"
            , ""
            , "static inline " ++ cType ++ " sbv_native_" ++ tag ++ "_binary(" ++ cType ++ " a, " ++ cType ++ " b, bf_rnd_t rnd, int op)"
            , "{"
            , "  bf_context_t ctx; bf_t x, y, r; " ++ cType ++ " result;"
            , "  bf_context_init(&ctx, sbv_native_bf_realloc, NULL); bf_init(&ctx, &x); bf_init(&ctx, &y); bf_init(&ctx, &r);"
            , "  bf_set_float64(&x, (double) a); bf_set_float64(&y, (double) b);"
            , "  if (op == 0) bf_add(&r, &x, &y, " ++ show precision ++ ", sbv_native_" ++ tag ++ "_flags(rnd));"
            , "  else if (op == 1) bf_sub(&r, &x, &y, " ++ show precision ++ ", sbv_native_" ++ tag ++ "_flags(rnd));"
            , "  else if (op == 2) bf_mul(&r, &x, &y, " ++ show precision ++ ", sbv_native_" ++ tag ++ "_flags(rnd));"
            , "  else bf_div(&r, &x, &y, " ++ show precision ++ ", sbv_native_" ++ tag ++ "_flags(rnd));"
            , "  result = sbv_native_" ++ tag ++ "_finish(&r, rnd);"
            , "  bf_delete(&r); bf_delete(&y); bf_delete(&x); bf_context_end(&ctx); return result;"
            , "}"
            , ""
            ]
         ++ concatMap (binaryWrapper cType tag) [("add", 0), ("sub", 1), ("mul", 2), ("div", 3)]
         ++ ["static inline " ++ cType ++ " sbv_native_" ++ tag ++ "_sqrt(" ++ cType ++ " a, bf_rnd_t rnd)"
            , "{"
            , "  bf_context_t ctx; bf_t x, r; " ++ cType ++ " result;"
            , "  bf_context_init(&ctx, sbv_native_bf_realloc, NULL); bf_init(&ctx, &x); bf_init(&ctx, &r); bf_set_float64(&x, (double) a);"
            , "  bf_sqrt(&r, &x, " ++ show precision ++ ", sbv_native_" ++ tag ++ "_flags(rnd)); result = sbv_native_" ++ tag ++ "_finish(&r, rnd);"
            , "  bf_delete(&r); bf_delete(&x); bf_context_end(&ctx); return result;"
            , "}"
            , ""
            , "static inline " ++ cType ++ " sbv_native_" ++ tag ++ "_round(" ++ cType ++ " a, bf_rnd_t rnd)"
            , "{"
            , "  bf_context_t ctx; bf_t x; " ++ cType ++ " result;"
            , "  bf_context_init(&ctx, sbv_native_bf_realloc, NULL); bf_init(&ctx, &x); bf_set_float64(&x, (double) a);"
            , "  bf_rint(&x, rnd); result = sbv_native_" ++ tag ++ "_finish(&x, rnd);"
            , "  bf_delete(&x); bf_context_end(&ctx); return result;"
            , "}"
            , ""
            , "static inline " ++ cType ++ " sbv_native_" ++ tag ++ "_fma(" ++ cType ++ " a, " ++ cType ++ " b, " ++ cType ++ " c, bf_rnd_t rnd)"
            , "{"
            , "  bf_context_t ctx; bf_t x, y, z, r; " ++ cType ++ " result;"
            , "  bf_context_init(&ctx, sbv_native_bf_realloc, NULL); bf_init(&ctx, &x); bf_init(&ctx, &y); bf_init(&ctx, &z); bf_init(&ctx, &r);"
            , "  bf_set_float64(&x, (double) a); bf_set_float64(&y, (double) b); bf_set_float64(&z, (double) c);"
            , "  bf_mul(&r, &x, &y, BF_PREC_INF, BF_FLAG_EXT_EXP | BF_RNDN);"
            , "  bf_add(&r, &r, &z, " ++ show precision ++ ", sbv_native_" ++ tag ++ "_flags(rnd)); result = sbv_native_" ++ tag ++ "_finish(&r, rnd);"
            , "  bf_delete(&r); bf_delete(&z); bf_delete(&y); bf_delete(&x); bf_context_end(&ctx); return result;"
            , "}"
            , ""
            ]

       binaryWrapper :: String -> String -> (String, Int) -> [String]
       binaryWrapper cType tag (suffix, operation) =
         ["static inline " ++ cType ++ " sbv_native_" ++ tag ++ "_" ++ suffix ++ "(" ++ cType ++ " a, " ++ cType ++ " b, bf_rnd_t rnd)"
         , "{ return sbv_native_" ++ tag ++ "_binary(a, b, rnd, " ++ show operation ++ "); }"
         , ""]

-- | Lower explicitly rounded native floating-point arithmetic. RNE remains a
-- direct native C operation under the public FE_TONEAREST calling convention;
-- other constants and symbolic modes use LibBF without changing hardware
-- rounding. The caller precondition is not checked at runtime.
nativeFPExpr :: [(SV, CV)] -> Op -> [SV] -> Kind -> [Doc] -> Maybe CLowering
nativeFPExpr consts (IEEEFP fpOp) svs resultKind args
  | resultKind `elem` [KFloat, KDouble]
  = case (fpOp, args, svs) of
      (FP_Add             , [_rm, a, b]   , r:_) | needsAdapter r -> lower "add"   [a, b] r
      (FP_Sub             , [_rm, a, b]   , r:_) | needsAdapter r -> lower "sub"   [a, b] r
      (FP_Mul             , [_rm, a, b]   , r:_) | needsAdapter r -> lower "mul"   [a, b] r
      (FP_Div             , [_rm, a, b]   , r:_) | needsAdapter r -> lower "div"   [a, b] r
      (FP_FMA             , [_rm, a, b, c], r:_) | needsAdapter r -> lower "fma"   [a, b, c] r
      (FP_Sqrt            , [_rm, a]      , r:_) | needsAdapter r -> lower "sqrt"  [a] r
      (FP_RoundToIntegral , [_rm, a]      , r:_) | needsAdapter r -> lower "round" [a] r
      _                                                           -> Nothing
  | True = Nothing
 where lower suffix values rm = Just . expressionLowering
                                   [CRequiresLibBF, CRequiresLibM, CRequiresNativeFPRounding]
                                 $ namedCall (nativePrefix resultKind ++ suffix)
                                             (values ++ [nativeBFRoundingMode consts rm])

       needsAdapter rm = case rm `lookup` consts of
         Just (CV k (CADT ("RoundNearestTiesToEven", []))) | isRoundingMode k -> False
         Just (CV k (CADT (_, [])))                        | isRoundingMode k -> True
         Nothing                                           | isRoundingMode rm -> True
         _ -> error $ "SBV->C: Expected a rounding mode, received " ++ show rm

       nativePrefix KFloat  = "sbv_native_float_"
       nativePrefix KDouble = "sbv_native_double_"
       nativePrefix k       = error $ "SBV->C: Expected a native floating-point kind, received " ++ show k
nativeFPExpr _ _ _ _ _ = Nothing

-- | Render a LibBF rounding mode for a native floating-point adapter.
nativeBFRoundingMode :: [(SV, CV)] -> SV -> Doc
nativeBFRoundingMode consts sv = case sv `lookup` consts of
  Just (CV k (CADT (rmName, [])))
    | isRoundingMode k -> maybe bad (text . snd) (lookup rmName roundingModeNames)
  Nothing
    | isRoundingMode sv -> namedCall "sbv_native_bf_rounding_mode" [text (show sv)]
  _                     -> bad
 where bad = error $ "SBV->C: Expected a rounding mode, received " ++ show sv

-- | Canonicalize externally supplied raw bits by clearing unused high bits.
arbitraryFPNormalize :: Kind -> Doc -> Doc
arbitraryFPNormalize k value = namedCall (prefix k ++ "_norm") [value]

-- | Print arbitrary floating-point interchange bits as fixed-width hexadecimal.
arbitraryFPPrint :: Kind -> Doc -> Doc
arbitraryFPPrint k value = namedCall (prefix k ++ "_fprint") [text "stdout", value]

-- | Compare two arbitrary floating-point interchange values using SMT object
-- equality: all NaNs compare equal and the two signed zeroes remain distinct.
arbitraryFPObjectEqual :: Kind -> Doc -> Doc -> Doc
arbitraryFPObjectEqual k left right = namedCall (prefix k ++ "_obj_eq") [left, right]

-- | Classify a raw arbitrary-format value without performing arithmetic.
arbitraryFPIsNaN :: Kind -> Doc -> Doc
arbitraryFPIsNaN kind value = namedCall (prefix kind ++ "_is_nan") [value]

-- | Compare two arbitrary floating-point values using IEEE equality.
arbitraryFPEqual :: Kind -> Doc -> Doc -> Doc
arbitraryFPEqual k left right = namedCall (prefix k ++ "_eq") [left, right]

-- | Compare two native floating-point values using SMT object equality: all
-- NaNs compare equal and the two signed zeroes remain distinct.
nativeFPObjectEqual :: Doc -> Doc -> Doc
nativeFPObjectEqual left right = choose (renderedIsNaN left) (renderedIsNaN right)
                              $ choose (renderedIsNegativeZero left) (renderedIsNegativeZero right)
                              $ choose (renderedIsNegativeZero right) (renderedIsNegativeZero left) (equal left right)
 where choose condition ifTrue ifFalse = condition <+> text "?" <+> ifTrue <+> text ":" <+> ifFalse
       renderedIsNaN value          = text "isnan" P.<> parens value
       equal x y                    = parens (x <+> text "==" <+> y)
       renderedIsNegativeZero value = parens (text "signbit" P.<> parens value <+> text "&&" <+> equal value (text "0"))

-- | Return the public C type name for an arbitrary floating-point kind.
arbitraryFPCType :: Kind -> String
arbitraryFPCType (KFP eb sb) = "SFP" ++ show eb ++ "_" ++ show sb
arbitraryFPCType k           = error $ "SBV->C: Expected an arbitrary floating-point kind, received " ++ show k

-- | A bit-preserving conversion between a floating-point interchange value
-- and a bit-vector of the same width.
data Reinterpret = Reinterpret Kind Kind deriving Eq

-- | A value conversion implemented by the LibBF runtime.
data FloatCast = FloatCast Kind Kind deriving Eq

-- | Emit a bit-preserving conversion between raw C representations.
reinterpretRuntime :: Reinterpret -> [String]
reinterpretRuntime (Reinterpret fr to)
  | reprWidth fr /= reprWidth to = error $ "SBV->C: Cannot reinterpret representations of different widths: " ++ show (fr, to)
  | True =
      ["static inline " ++ reprCType to ++ " " ++ reinterpretName fr to ++ "(" ++ reprCType fr ++ " a)"
      , "{"
      , "  " ++ reprCType to ++ " r = " ++ reprZero to ++ "; uint64_t i;"
      , "  for (i = 0; i < " ++ show (reprWidth to) ++ "; ++i) { " ++ reprSetBit to "r" "i" (reprGetBit fr "a" "i") ++ " }"
      , "  return " ++ reprNormalize to "r" ++ ";"
      , "}"
      , ""]

-- | Construct the collision-free name of a reinterpretation helper.
reinterpretName :: Kind -> Kind -> String
reinterpretName fr to = "sbv_fp_reinterpret_" ++ reprTag fr ++ "_" ++ reprTag to

-- | Resolve explicit native mappings for numeric conversion helpers. A native
-- real mapping to long double has no fixed SBV IEEE kind; retain 'KReal' so the
-- conversion can report that unsupported bridge instead of narrowing silently.
floatCastKind :: CgConfig -> Kind -> Kind
floatCastKind cfg KReal = case cgReal cfg of
                           Just CgFloat  -> KFloat
                           Just CgDouble -> KDouble
                           _             -> KReal
floatCastKind cfg kind = mappedIntegerKind (cgInteger cfg) kind

-- | Test whether a cast crosses an explicitly mapped floating representation,
-- including integer mappings used as a floating-point source or destination.
mappedFloatCast :: CgConfig -> Kind -> Kind -> Bool
mappedFloatCast cfg fr to
  | Just CgLongDouble <- cgReal cfg
  , KReal `elem` [fr, to] = False
  | True                 = (from /= fr || target /= to || mappedReal)
                        && (floating from || floating target || mappedReal)
 where from   = floatCastKind cfg fr
       target = floatCastKind cfg to
       floating kind = isFP kind || isFloat kind || isDouble kind
       mappedReal = KReal `elem` [fr, to] && case cgReal cfg of
                                             Just{}  -> True
                                             Nothing -> False

-- | Emit a LibBF-backed value conversion between supported numeric formats.
castRuntime :: CgConfig -> FloatCast -> [String]
castRuntime cfg (FloatCast source target) = case (fr, to) of
  (KFP{}, KFP{}) ->
    ["static inline " ++ reprCType to ++ " " ++ helperName ++ "(" ++ reprCType fr ++ " a, bf_rnd_t rnd)"
    , "{"
    , "  bf_context_t ctx; bf_t x; " ++ reprCType to ++ " raw;"
    , "  bf_context_init(&ctx, sbv_bf_realloc, NULL); " ++ prefix fr ++ "_decode(&ctx, &x, a);"
    , "  bf_round(&x, " ++ show (significandBits to) ++ ", " ++ prefix to ++ "_flags(rnd)); raw = " ++ prefix to ++ "_encode(&x);"
    , "  bf_delete(&x); bf_context_end(&ctx); return raw;"
    , "}"
    , ""]
  (KFloat, KFP{})     -> fromNative "SFloat"
  (KDouble, KFP{})    -> fromNative "SDouble"
  (KFP{}, KFloat)     -> toNative "SFloat" True
  (KFP{}, KDouble)    -> toNative "SDouble" False
  _ | isNativeFloat fr && isNativeFloat to      -> nativeToNative
  _ | isExactGMPKind cfg fr && isNativeFloat to -> exactToNative
  _ | isNativeFloat fr && isExactGMPKind cfg to -> nativeToExact
  _ | isExactGMPKind cfg fr && isFP to -> exactToFP
  _ | isFP fr && isExactGMPKind cfg to -> fpToExact
  _ | isBounded fr && isSomeFloat to -> integerToFP
  _ | isSomeFloat fr && isBounded to -> fpToInteger
  _ | Just CgLongDouble <- cgReal cfg
    , KReal `elem` [source, target]
    -> error "SBV->C: Numeric conversions involving cgSRealType CgLongDouble are not yet supported; use CgFloat, CgDouble, or exact GMP reals."
  _                   -> error $ "SBV->C: Unsupported arbitrary floating-point cast: " ++ show (fr, to)
 where fr = floatCastKind cfg source
       to = floatCastKind cfg target
       helperName = castName source target

       fromNative sourceType =
         ["static inline " ++ reprCType to ++ " " ++ helperName ++ "(" ++ sourceType ++ " a, bf_rnd_t rnd)"
         , "{"
         , "  bf_context_t ctx; bf_t x; " ++ reprCType to ++ " raw;"
         , "  bf_context_init(&ctx, sbv_bf_realloc, NULL); bf_init(&ctx, &x); bf_set_float64(&x, (double) a);"
         , "  bf_round(&x, " ++ show (significandBits to) ++ ", " ++ prefix to ++ "_flags(rnd)); raw = " ++ prefix to ++ "_encode(&x);"
         , "  bf_delete(&x); bf_context_end(&ctx); return raw;"
         , "}"
         , ""]

       toNative targetType singlePrecision =
            ["static inline " ++ targetType ++ " " ++ helperName ++ "(" ++ reprCType fr ++ " a, bf_rnd_t rnd)"
            , "{"
            , "  bf_context_t ctx; bf_t x; double result;"
            , "  bf_context_init(&ctx, sbv_bf_realloc, NULL); " ++ prefix fr ++ "_decode(&ctx, &x, a);"
            ]
         ++ ["  bf_round(&x, 24, BF_FLAG_SUBNORMAL | bf_set_exp_bits(8) | (bf_flags_t) rnd);" | singlePrecision]
         ++ ["  bf_get_float64(&x, &result, rnd); bf_delete(&x); bf_context_end(&ctx); return (" ++ targetType ++ ") result;"
            , "}"
            , ""]

       nativeToNative =
         ["static inline " ++ nativeCType to ++ " " ++ helperName ++ "(" ++ nativeCType fr ++ " a, bf_rnd_t rnd)"
         , "{"
         , "  bf_context_t ctx; bf_t x; double result;"
         , "  bf_context_init(&ctx, sbv_bf_realloc, NULL); bf_init(&ctx, &x); bf_set_float64(&x, (double) a);"
         , "  bf_round(&x, " ++ show (significandBits to) ++ ", " ++ nativeFlags to ++ "); bf_get_float64(&x, &result, rnd);"
         , "  bf_delete(&x); bf_context_end(&ctx); return (" ++ nativeCType to ++ ") result;"
         , "}"
         , ""]

       integerToFP =
         ["static inline " ++ floatingCType to ++ " " ++ helperName ++ "(" ++ reprCType fr ++ " a, bf_rnd_t rnd)"
         , "{"
         , "  uint64_t words[" ++ show sourceWords ++ "]; uint64_t carry = 1; size_t i; limb_t j;"
         , "  const bool negative = " ++ (if hasSign fr then reprGetBit fr "a" (show (reprWidth fr - 1)) else "false") ++ ";"
         , "  bf_context_t ctx; bf_t x, chunk;" ++ integerResultDeclaration
         , "  for (i = 0; i < " ++ show sourceWords ++ "; ++i) {"
         , "    words[i] = 0;"
         , "    for (j = 0; j < 64 && i * 64 + j < " ++ show (reprWidth fr) ++ "; ++j)"
         , "      if (" ++ reprGetBit fr "a" "(i * 64 + j)" ++ ") words[i] |= UINT64_C(1) << j;"
         , "  }"
         , "  if (negative) for (i = 0; i < " ++ show sourceWords ++ "; ++i) {"
         , "    const uint64_t next = ~words[i] + carry; carry = carry && next == 0; words[i] = next;"
         , "  }"
         , "  words[" ++ show (sourceWords - 1) ++ "] &= " ++ u64 (reprTopMask fr) ++ ";"
         , "  bf_context_init(&ctx, sbv_bf_realloc, NULL); bf_init(&ctx, &x); bf_init(&ctx, &chunk); bf_set_ui(&x, 0);"
         , "  for (i = " ++ show sourceWords ++ "; i-- > 0;) {"
         , "    bf_mul_2exp(&x, i == " ++ show (sourceWords - 1) ++ " ? " ++ show sourceTopBits ++ " : 64, BF_PREC_INF, BF_FLAG_EXT_EXP | BF_RNDZ);"
         , "    bf_set_ui(&chunk, words[i]); bf_add(&x, &x, &chunk, BF_PREC_INF, BF_FLAG_EXT_EXP | BF_RNDZ);"
         , "  }"
         , "  if (negative) bf_neg(&x);"
         , "  bf_round(&x, " ++ show (significandBits to) ++ ", " ++ floatingFlags to ++ ");" ++ integerFinish
         , "  bf_delete(&chunk); bf_delete(&x); bf_context_end(&ctx); return " ++ integerResult ++ ";"
         , "}"
         , ""]

       fpToInteger =
         ["static inline " ++ reprCType to ++ " " ++ helperName ++ "(" ++ floatingCType fr ++ " a, bf_rnd_t rnd)"
         , "{"
         , "  bf_context_t ctx; bf_t x; " ++ reprCType integerBits ++ " raw = " ++ reprZero integerBits ++ "; limb_t i;"
         , "  bf_context_init(&ctx, sbv_bf_realloc, NULL); " ++ decodeFloating fr ++ " bf_rint(&x, rnd);"
         , "  if (bf_is_finite(&x) && !bf_is_zero(&x)) {"
         , "    const slimb_t base = (slimb_t) x.len * LIMB_BITS;"
         , "    for (i = 0; i < " ++ show (reprWidth to) ++ "; ++i) {"
         , "      const slimb_t bit = (slimb_t) i - x.expn + base;"
         , "      if (bit >= 0 && bit < base) { " ++ reprSetBit integerBits "raw" "i" "((x.tab[bit / LIMB_BITS] >> (bit % LIMB_BITS)) & 1) != 0" ++ " }"
         , "    }"
         , "    if (x.sign) raw = " ++ negateRepr integerBits "raw" ++ ";"
         , "  }"
         , "  bf_delete(&x); bf_context_end(&ctx);"
         , if integerBits /= to
              then "  " ++ reprCType to ++ " result; memcpy(&result, &raw, sizeof result); return result;"
              else "  return " ++ reprNormalize to "raw" ++ ";"
         , "}"
         , ""]

       -- Reconstruct native signed results through their unsigned object
       -- representation, avoiding implementation-defined unsigned-to-signed casts.
       integerBits
         | KBounded True width <- to
         , not (isWideBV to) = KBounded False width
         | True             = to

       exactToFP
         | fr == KUnbounded =
            ["static inline " ++ reprCType to ++ " " ++ helperName ++ "(SInteger a, bf_rnd_t rnd)"
            , "{"
            , "  bf_context_t ctx; bf_t x, chunk; " ++ reprCType to ++ " raw;"
            , "  bf_context_init(&ctx, sbv_bf_realloc, NULL); bf_init(&ctx, &x); bf_init(&ctx, &chunk);"
            , "  sbv_bf_set_mpz(&x, &chunk, a); bf_round(&x, " ++ show (significandBits to) ++ ", " ++ prefix to ++ "_flags(rnd));"
            , "  raw = " ++ prefix to ++ "_encode(&x); bf_delete(&chunk); bf_delete(&x); bf_context_end(&ctx); return raw;"
            , "}"
            , ""]
         | fr == KReal =
            ["static inline " ++ reprCType to ++ " " ++ helperName ++ "(SReal a, bf_rnd_t rnd)"
            , "{"
            , "  bf_context_t ctx; bf_t x, numerator, denominator, chunk; " ++ reprCType to ++ " raw;"
            , "  bf_context_init(&ctx, sbv_bf_realloc, NULL); bf_init(&ctx, &x); bf_init(&ctx, &numerator); bf_init(&ctx, &denominator); bf_init(&ctx, &chunk);"
            , "  sbv_bf_set_mpz(&numerator, &chunk, mpq_numref(a)); sbv_bf_set_mpz(&denominator, &chunk, mpq_denref(a));"
            , "  bf_div(&x, &numerator, &denominator, " ++ show (significandBits to) ++ ", " ++ prefix to ++ "_flags(rnd)); raw = " ++ prefix to ++ "_encode(&x);"
            , "  bf_delete(&chunk); bf_delete(&denominator); bf_delete(&numerator); bf_delete(&x); bf_context_end(&ctx); return raw;"
            , "}"
            , ""]
         | otherwise = error $ "SBV->C: Expected an exact GMP source kind, received " ++ show fr

       fpToExact
         | to == KUnbounded =
            ["static inline SInteger " ++ helperName ++ "(sbv_gmp_ctx *gmp_ctx, " ++ reprCType fr ++ " a, bf_rnd_t rnd)"
            , "{"
            , "  bf_context_t ctx; bf_t x; mpz_ptr result = sbv_gmp_new_integer(gmp_ctx);"
            , "  bf_context_init(&ctx, sbv_bf_realloc, NULL); " ++ prefix fr ++ "_decode(&ctx, &x, a); bf_rint(&x, rnd);"
            , "  sbv_bf_get_mpz(result, &x); bf_delete(&x); bf_context_end(&ctx); return result;"
            , "}"
            , ""]
         | to == KReal =
            ["static inline SReal " ++ helperName ++ "(sbv_gmp_ctx *gmp_ctx, " ++ reprCType fr ++ " a, bf_rnd_t rnd)"
            , "{"
            , "  bf_context_t ctx; bf_t x; mpq_ptr result = sbv_gmp_new_real(gmp_ctx);"
            , "  (void) rnd; bf_context_init(&ctx, sbv_bf_realloc, NULL); " ++ prefix fr ++ "_decode(&ctx, &x, a);"
            , "  sbv_bf_get_mpq(result, &x); bf_delete(&x); bf_context_end(&ctx); return result;"
            , "}"
            , ""]
         | otherwise = error $ "SBV->C: Expected an exact GMP target kind, received " ++ show to

       exactToNative
         | fr == KUnbounded =
            ["static inline " ++ nativeCType to ++ " " ++ helperName ++ "(SInteger a, bf_rnd_t rnd)"
            , "{"
            , "  bf_context_t ctx; bf_t x, chunk; double result;"
            , "  bf_context_init(&ctx, sbv_bf_realloc, NULL); bf_init(&ctx, &x); bf_init(&ctx, &chunk); sbv_bf_set_mpz(&x, &chunk, a);"
            , "  bf_round(&x, " ++ show (significandBits to) ++ ", " ++ nativeFlags to ++ "); bf_get_float64(&x, &result, rnd);"
            , "  bf_delete(&chunk); bf_delete(&x); bf_context_end(&ctx); return (" ++ nativeCType to ++ ") result;"
            , "}"
            , ""]
         | fr == KReal =
            ["static inline " ++ nativeCType to ++ " " ++ helperName ++ "(SReal a, bf_rnd_t rnd)"
            , "{"
            , "  bf_context_t ctx; bf_t x, numerator, denominator, chunk; double result;"
            , "  bf_context_init(&ctx, sbv_bf_realloc, NULL); bf_init(&ctx, &x); bf_init(&ctx, &numerator); bf_init(&ctx, &denominator); bf_init(&ctx, &chunk);"
            , "  sbv_bf_set_mpz(&numerator, &chunk, mpq_numref(a)); sbv_bf_set_mpz(&denominator, &chunk, mpq_denref(a));"
            , "  bf_div(&x, &numerator, &denominator, " ++ show (significandBits to) ++ ", " ++ nativeFlags to ++ "); bf_get_float64(&x, &result, rnd);"
            , "  bf_delete(&chunk); bf_delete(&denominator); bf_delete(&numerator); bf_delete(&x); bf_context_end(&ctx); return (" ++ nativeCType to ++ ") result;"
            , "}"
            , ""]
         | otherwise = error $ "SBV->C: Expected an exact GMP source kind, received " ++ show fr

       nativeToExact
         | to == KUnbounded =
            ["static inline SInteger " ++ helperName ++ "(sbv_gmp_ctx *gmp_ctx, " ++ nativeCType fr ++ " a, bf_rnd_t rnd)"
            , "{"
            , "  bf_context_t ctx; bf_t x; mpz_ptr result = sbv_gmp_new_integer(gmp_ctx);"
            , "  bf_context_init(&ctx, sbv_bf_realloc, NULL); bf_init(&ctx, &x); bf_set_float64(&x, (double) a); bf_rint(&x, rnd);"
            , "  sbv_bf_get_mpz(result, &x); bf_delete(&x); bf_context_end(&ctx); return result;"
            , "}"
            , ""]
         | to == KReal =
            ["static inline SReal " ++ helperName ++ "(sbv_gmp_ctx *gmp_ctx, " ++ nativeCType fr ++ " a, bf_rnd_t rnd)"
            , "{"
            , "  bf_context_t ctx; bf_t x; mpq_ptr result = sbv_gmp_new_real(gmp_ctx);"
            , "  (void) rnd; bf_context_init(&ctx, sbv_bf_realloc, NULL); bf_init(&ctx, &x); bf_set_float64(&x, (double) a);"
            , "  sbv_bf_get_mpq(result, &x); bf_delete(&x); bf_context_end(&ctx); return result;"
            , "}"
            , ""]
         | otherwise = error $ "SBV->C: Expected an exact GMP target kind, received " ++ show to

       nativeFlags KFloat  = "BF_FLAG_SUBNORMAL | bf_set_exp_bits(8) | (bf_flags_t) rnd"
       nativeFlags KDouble = "BF_FLAG_SUBNORMAL | bf_set_exp_bits(11) | (bf_flags_t) rnd"
       nativeFlags k       = error $ "SBV->C: Expected a native floating-point kind, received " ++ show k

       nativeCType KFloat  = "SFloat"
       nativeCType KDouble = "SDouble"
       nativeCType k       = error $ "SBV->C: Expected a native floating-point kind, received " ++ show k

       isNativeFloat k = k == KFloat || k == KDouble

       isSomeFloat k = isFP k || isNativeFloat k

       floatingCType k
         | isFP k          = reprCType k
         | isNativeFloat k = nativeCType k
         | otherwise       = error $ "SBV->C: Expected a floating-point kind, received " ++ show k

       floatingFlags k
         | isFP k          = prefix k ++ "_flags(rnd)"
         | isNativeFloat k = nativeFlags k
         | otherwise       = error $ "SBV->C: Expected a floating-point kind, received " ++ show k

       decodeFloating k
         | isFP k          = prefix k ++ "_decode(&ctx, &x, a);"
         | isNativeFloat k = "bf_init(&ctx, &x); bf_set_float64(&x, (double) a);"
         | otherwise       = error $ "SBV->C: Expected a floating-point kind, received " ++ show k

       integerResultDeclaration
         | isFP to          = " " ++ reprCType to ++ " raw;"
         | isNativeFloat to = " double result;"
         | otherwise        = error $ "SBV->C: Expected a floating-point target kind, received " ++ show to

       integerFinish
         | isFP to          = " raw = " ++ prefix to ++ "_encode(&x);"
         | isNativeFloat to = " bf_get_float64(&x, &result, rnd);"
         | otherwise        = error $ "SBV->C: Expected a floating-point target kind, received " ++ show to

       integerResult
         | isFP to          = "raw"
         | isNativeFloat to = "(" ++ nativeCType to ++ ") result"
         | otherwise        = error $ "SBV->C: Expected a floating-point target kind, received " ++ show to

       sourceWords   = (reprWidth fr + 63) `div` 64
       sourceTopBits = let r = reprWidth fr `mod` 64 in if r == 0 then 64 else r

-- | Emit conversion primitives shared by LibBF/GMP value casts.
exactBridgeRuntime :: [String]
exactBridgeRuntime =
  ["static void sbv_bf_set_mpz(bf_t *result, bf_t *chunk, mpz_srcptr value)"
  , "{"
  , "  const size_t count = (mpz_sizeinbase(value, 2) + 63) / 64; size_t written = 0, i;"
  , "  uint64_t *words; bf_set_ui(result, 0);"
  , "  if (mpz_sgn(value) == 0) return;"
  , "  words = (uint64_t *) calloc(count, sizeof(*words)); if (words == NULL) abort();"
  , "  mpz_export(words, &written, -1, sizeof(*words), 0, 0, value);"
  , "  for (i = written; i-- > 0;) {"
  , "    bf_mul_2exp(result, 64, BF_PREC_INF, BF_FLAG_EXT_EXP | BF_RNDZ);"
  , "    bf_set_ui(chunk, words[i]); bf_add(result, result, chunk, BF_PREC_INF, BF_FLAG_EXT_EXP | BF_RNDZ);"
  , "  }"
  , "  free(words); if (mpz_sgn(value) < 0) bf_neg(result);"
  , "}"
  , ""
  , "static void sbv_bf_get_mpz(mpz_ptr result, const bf_t *value)"
  , "{"
  , "  slimb_t shift; mpz_set_ui(result, 0);"
  , "  if (!bf_is_finite(value) || bf_is_zero(value)) return;"
  , "  mpz_import(result, value->len, -1, sizeof(*value->tab), 0, 0, value->tab);"
  , "  shift = value->expn - (slimb_t) value->len * LIMB_BITS;"
  , "  if (shift >= 0) mpz_mul_2exp(result, result, (mp_bitcnt_t) shift);"
  , "  else mpz_tdiv_q_2exp(result, result, (mp_bitcnt_t) -shift);"
  , "  if (value->sign) mpz_neg(result, result);"
  , "}"
  , ""
  , "static void sbv_bf_get_mpq(mpq_ptr result, const bf_t *value)"
  , "{"
  , "  slimb_t shift; mpq_set_ui(result, 0, 1);"
  , "  if (!bf_is_finite(value) || bf_is_zero(value)) return;"
  , "  mpz_import(mpq_numref(result), value->len, -1, sizeof(*value->tab), 0, 0, value->tab);"
  , "  shift = value->expn - (slimb_t) value->len * LIMB_BITS;"
  , "  if (shift >= 0) mpz_mul_2exp(mpq_numref(result), mpq_numref(result), (mp_bitcnt_t) shift);"
  , "  else mpz_mul_2exp(mpq_denref(result), mpq_denref(result), (mp_bitcnt_t) -shift);"
  , "  if (value->sign) mpz_neg(mpq_numref(result), mpq_numref(result)); mpq_canonicalize(result);"
  , "}"
  , ""]

-- | Construct the collision-free name of a floating-point value conversion.
castName :: Kind -> Kind -> String
castName fr to = "sbv_fp_cast_" ++ castTag fr ++ "_" ++ castTag to

-- | Return the generated tag used in a floating-point value conversion.
castTag :: Kind -> String
castTag k@KFP{}    = reprTag k
castTag KFloat     = "float"
castTag KDouble    = "double"
castTag KUnbounded = "integer"
castTag KReal      = "real"
castTag k          = reprTag k

-- | Return the significand width of an arbitrary floating-point kind.
significandBits :: Kind -> Int
significandBits (KFP _ sb) = sb
significandBits KFloat     = 24
significandBits KDouble    = 53
significandBits k          = error $ "SBV->C: Expected a floating-point kind, received " ++ show k

-- | Render modular negation of a raw bit-vector representation.
negateRepr :: Kind -> String -> String
negateRepr k value
  | isWideBV k  = bvPrefix k ++ "_neg(" ++ value ++ ")"
  | isBounded k = "(" ++ reprCType k ++ ") (~(uint64_t) " ++ value ++ " + UINT64_C(1))"
  | otherwise   = error $ "SBV->C: Cannot negate " ++ show k

-- | Return the mask for the high limb of a raw bit-vector representation.
reprTopMask :: Kind -> Integer
reprTopMask k
  | r == 0    = (1 `shiftL` 64) - 1
  | otherwise = (1 `shiftL` r) - 1
 where r = reprWidth k `mod` 64

-- | Return the bit width of a raw floating-point or bit-vector representation.
reprWidth :: Kind -> Int
reprWidth k
  | isFP k || isBounded k = intSizeOf k
  | otherwise             = error $ "SBV->C: Expected a raw floating-point or bit-vector representation, received " ++ show k

-- | Return the C type used by a raw floating-point or bit-vector representation.
reprCType :: Kind -> String
reprCType k@KFP{}            = arbitraryFPCType k
reprCType (KBounded False 1) = "SBool"
reprCType (KBounded False w) = "SWord" ++ show w
reprCType (KBounded True  w) = "SInt" ++ show w
reprCType k                  = error $ "SBV->C: Expected a raw floating-point or bit-vector representation, received " ++ show k

-- | Return the generated tag for a raw representation.
reprTag :: Kind -> String
reprTag (KFP eb sb)          = "f" ++ show eb ++ "_" ++ show sb
reprTag (KBounded False w)   = "u" ++ show w
reprTag (KBounded True  w)   = "s" ++ show w
reprTag k                    = error $ "SBV->C: Expected a raw floating-point or bit-vector representation, received " ++ show k

-- | Render a bit read from a raw representation.
reprGetBit :: Kind -> String -> String -> String
reprGetBit k@KFP{} value bit = prefix k ++ "_get(" ++ value ++ ", " ++ bit ++ ")"
reprGetBit k value bit
  | isWideBV k  = bvPrefix k ++ "_get(" ++ value ++ ", " ++ bit ++ ")"
  | isBounded k = "((((uint64_t) " ++ value ++ ") >> (" ++ bit ++ ")) & UINT64_C(1)) != 0"
  | otherwise   = error $ "SBV->C: Cannot read bits from " ++ show k

-- | Render a bit update to a raw representation.
reprSetBit :: Kind -> String -> String -> String -> String
reprSetBit k@KFP{} value bit bitValue = prefix k ++ "_set(&" ++ value ++ ", " ++ bit ++ ", " ++ bitValue ++ ");"
reprSetBit k value bit bitValue
  | isWideBV k  = bvPrefix k ++ "_set(&" ++ value ++ ", " ++ bit ++ ", " ++ bitValue ++ ");"
  | isBounded k = value ++ " = (" ++ reprCType k ++ ") ((uint64_t) " ++ value ++ " | ((uint64_t) (" ++ bitValue ++ ") << (" ++ bit ++ ")));"
  | otherwise   = error $ "SBV->C: Cannot update bits in " ++ show k

-- | Render the zero value for a raw representation.
reprZero :: Kind -> String
reprZero k@KFP{} = prefix k ++ "_zero()"
reprZero k
  | isWideBV k  = bvPrefix k ++ "_zero()"
  | isBounded k = "(" ++ reprCType k ++ ") 0"
  | otherwise   = error $ "SBV->C: Cannot construct a zero of " ++ show k

-- | Render canonicalization for a raw representation.
reprNormalize :: Kind -> String -> String
reprNormalize k@KFP{} value = prefix k ++ "_norm(" ++ value ++ ")"
reprNormalize k value
  | isWideBV k  = bvPrefix k ++ "_norm(" ++ value ++ ")"
  | isBounded k = value
  | otherwise   = error $ "SBV->C: Cannot normalize " ++ show k

-- | Return the generated namespace prefix for an exact-width bit-vector.
bvPrefix :: Kind -> String
bvPrefix (KBounded False w) = "sbv_bv_u" ++ show w
bvPrefix (KBounded True  w) = "sbv_bv_s" ++ show w
bvPrefix k                  = error $ "SBV->C: Expected a bit-vector kind, received " ++ show k

-- | Emit all helpers associated with a single floating-point format.
formatRuntime :: Kind -> [String]
formatRuntime k@(KFP eb sb) =
  ["#if BF_EXP_BITS_MAX < " ++ show eb
  , "#error \"The selected LibBF build cannot represent " ++ arbitraryFPCType k ++ "\""
  , "#endif"
  , ""
  , "static inline " ++ ty ++ " " ++ p ++ "_zero(void)"
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
  , "static inline bool " ++ p ++ "_get(" ++ ty ++ " a, limb_t bit)"
  , "{"
  , "  return bit < " ++ show width ++ " && ((a.limb[bit / 64] >> (bit % 64)) & UINT64_C(1)) != 0;"
  , "}"
  , ""
  , "static inline void " ++ p ++ "_set(" ++ ty ++ " *a, limb_t bit, bool value)"
  , "{"
  , "  const uint64_t m = UINT64_C(1) << (bit % 64);"
  , "  if (value) { a->limb[bit / 64] |= m; } else { a->limb[bit / 64] &= ~m; }"
  , "}"
  , ""
  , "static inline uint64_t " ++ p ++ "_slice(" ++ ty ++ " a, limb_t offset, limb_t count)"
  , "{"
  , "  uint64_t r = 0; limb_t i;"
  , "  for (i = 0; i < count; ++i) if (" ++ p ++ "_get(a, offset + i)) r |= UINT64_C(1) << i;"
  , "  return r;"
  , "}"
  , ""
  , "static inline bool " ++ p ++ "_raw_eq(" ++ ty ++ " a, " ++ ty ++ " b)"
  , "{"
  , "  uint64_t r = 0; size_t i;"
  , "  for (i = 0; i < " ++ show n ++ "; ++i) r |= a.limb[i] ^ b.limb[i];"
  , "  return r == 0;"
  , "}"
  , ""
  , "static inline uint64_t " ++ p ++ "_exponent(" ++ ty ++ " a)"
  , "{"
  , "  return " ++ p ++ "_slice(a, " ++ show fracBits ++ ", " ++ show eb ++ ");"
  , "}"
  , ""
  , "static inline bool " ++ p ++ "_fraction_is_zero(" ++ ty ++ " a)"
  , "{"
  , "  limb_t i;"
  , "  for (i = 0; i < " ++ show fracBits ++ "; ++i) if (" ++ p ++ "_get(a, i)) return false;"
  , "  return true;"
  , "}"
  , ""
  , "static inline bool " ++ p ++ "_is_nan(" ++ ty ++ " a)"
  , "{ return " ++ p ++ "_exponent(a) == " ++ show expMask ++ " && !" ++ p ++ "_fraction_is_zero(a); }"
  , ""
  , "static inline bool " ++ p ++ "_is_infinite(" ++ ty ++ " a)"
  , "{ return " ++ p ++ "_exponent(a) == " ++ show expMask ++ " && " ++ p ++ "_fraction_is_zero(a); }"
  , ""
  , "static inline bool " ++ p ++ "_is_zero(" ++ ty ++ " a)"
  , "{ return " ++ p ++ "_exponent(a) == 0 && " ++ p ++ "_fraction_is_zero(a); }"
  , ""
  , "static inline bool " ++ p ++ "_is_subnormal(" ++ ty ++ " a)"
  , "{ return " ++ p ++ "_exponent(a) == 0 && !" ++ p ++ "_fraction_is_zero(a); }"
  , ""
  , "static inline bool " ++ p ++ "_is_normal(" ++ ty ++ " a)"
  , "{ const uint64_t e = " ++ p ++ "_exponent(a); return e != 0 && e != " ++ show expMask ++ "; }"
  , ""
  , "static inline bool " ++ p ++ "_is_negative(" ++ ty ++ " a)"
  , "{ return !" ++ p ++ "_is_nan(a) && " ++ p ++ "_get(a, " ++ show (width - 1) ++ "); }"
  , ""
  , "static inline bool " ++ p ++ "_is_positive(" ++ ty ++ " a)"
  , "{ return !" ++ p ++ "_is_nan(a) && !" ++ p ++ "_get(a, " ++ show (width - 1) ++ "); }"
  , ""
  , "static inline " ++ ty ++ " " ++ p ++ "_neg(" ++ ty ++ " a)"
  , "{ a.limb[" ++ show ((width - 1) `div` 64) ++ "] ^= UINT64_C(1) << " ++ show ((width - 1) `mod` 64) ++ "; return a; }"
  , ""
  , "static inline " ++ ty ++ " " ++ p ++ "_abs(" ++ ty ++ " a)"
  , "{ a.limb[" ++ show ((width - 1) `div` 64) ++ "] &= ~(UINT64_C(1) << " ++ show ((width - 1) `mod` 64) ++ "); return a; }"
  , ""
  , "static inline bool " ++ p ++ "_obj_eq(" ++ ty ++ " a, " ++ ty ++ " b)"
  , "{ return (" ++ p ++ "_is_nan(a) && " ++ p ++ "_is_nan(b)) || " ++ p ++ "_raw_eq(a, b); }"
  , ""
  , "static inline void " ++ p ++ "_decode(bf_context_t *ctx, bf_t *r, " ++ ty ++ " raw)"
  , "{"
  , "  const uint64_t e = " ++ p ++ "_exponent(raw);"
  , "  const bool sign = " ++ p ++ "_get(raw, " ++ show (width - 1) ++ ");"
  , "  bf_t chunk;"
  , "  bf_init(ctx, r); bf_init(ctx, &chunk);"
  , "  if (e == " ++ show expMask ++ ") {"
  , "    if (" ++ p ++ "_fraction_is_zero(raw)) bf_set_inf(r, sign); else bf_set_nan(r);"
  , "  } else if (e == 0 && " ++ p ++ "_fraction_is_zero(raw)) {"
  , "    bf_set_zero(r, sign);"
  , "  } else {"
  , "    bf_set_ui(r, e == 0 ? 0 : 1);"
  ]
  ++ concatMap decodeChunk chunks
  ++ ["    bf_mul_2exp(r, (slimb_t) e - " ++ show bias ++ " - " ++ show fracBits ++ " + (e == 0 ? 1 : 0), BF_PREC_INF, BF_FLAG_EXT_EXP | BF_RNDZ);"
     , "    if (sign) bf_neg(r);"
     , "  }"
     , "  bf_delete(&chunk);"
     , "}"
     , ""
     , "static inline " ++ ty ++ " " ++ p ++ "_encode(const bf_t *a)"
     , "{"
     , "  " ++ ty ++ " raw = " ++ p ++ "_zero(); limb_t i;"
     , "  if (bf_is_nan(a)) {"
     , "    for (i = 0; i < " ++ show eb ++ "; ++i) " ++ p ++ "_set(&raw, " ++ show fracBits ++ " + i, true);"
     , "    " ++ p ++ "_set(&raw, " ++ show (fracBits - 1) ++ ", true);"
     , "    return raw;"
     , "  }"
     , "  if (a->sign) " ++ p ++ "_set(&raw, " ++ show (width - 1) ++ ", true);"
     , "  if (a->expn == BF_EXP_INF) {"
     , "    for (i = 0; i < " ++ show eb ++ "; ++i) " ++ p ++ "_set(&raw, " ++ show fracBits ++ " + i, true);"
     , "    return raw;"
     , "  }"
     , "  if (a->expn != BF_EXP_ZERO) {"
     , "    const slimb_t biased = a->expn + " ++ show bias ++ " - 1;"
     , "    const bool normal = biased > 0;"
     , "    const uint64_t e = normal ? (uint64_t) biased : UINT64_C(0);"
     , "    const slimb_t base = (slimb_t) a->len * LIMB_BITS;"
     , "    for (i = 0; i < " ++ show eb ++ "; ++i) " ++ p ++ "_set(&raw, " ++ show fracBits ++ " + i, ((e >> i) & UINT64_C(1)) != 0);"
     , "    for (i = 0; i < " ++ show fracBits ++ "; ++i) {"
     , "      const slimb_t bit = normal ? base + (slimb_t) i - " ++ show sb
                                  ++ " : base + (slimb_t) i + 2 - " ++ show bias ++ " - " ++ show sb ++ " - a->expn;"
     , "      if (bit >= 0 && bit < base) " ++ p ++ "_set(&raw, i, ((a->tab[bit / LIMB_BITS] >> (bit % LIMB_BITS)) & 1) != 0);"
     , "    }"
     , "  }"
     , "  return raw;"
     , "}"
     , ""
     ]
  ++ arithmeticRuntime k
 where ty       = arbitraryFPCType k
       p        = prefix k
       width    = eb + sb
       fracBits = sb - 1
       n        = limbs k
       mask     = topMask k
       expMask  = (1 `shiftL` eb) - 1 :: Integer
       bias     = expMask `shiftR` 1
       chunks   = reverse [(offset, min 64 (fracBits - offset)) | offset <- [0, 64 .. fracBits - 1]]

       decodeChunk (offset, count) =
         ["    bf_mul_2exp(r, " ++ show count ++ ", BF_PREC_INF, BF_FLAG_EXT_EXP | BF_RNDZ);"
         , "    bf_set_ui(&chunk, " ++ p ++ "_slice(raw, " ++ show offset ++ ", " ++ show count ++ "));"
         , "    bf_add(r, r, &chunk, BF_PREC_INF, BF_FLAG_EXT_EXP | BF_RNDZ);"
         ]
formatRuntime k = error $ "SBV->C: Expected an arbitrary floating-point kind, received " ++ show k

-- | Emit arithmetic and comparison adapters for one floating-point format.
arithmeticRuntime :: Kind -> [String]
arithmeticRuntime k@(KFP eb sb) =
  ["static inline bf_flags_t " ++ p ++ "_flags(bf_rnd_t rnd)"
  , "{ return (bf_flags_t) rnd | BF_FLAG_SUBNORMAL | bf_set_exp_bits(" ++ show eb ++ "); }"
  , ""
  , "static inline " ++ ty ++ " " ++ p ++ "_binary(" ++ ty ++ " a, " ++ ty ++ " b, bf_rnd_t rnd, int op)"
  , "{"
  , "  bf_context_t ctx; bf_t x, y, r; " ++ ty ++ " raw;"
  , "  bf_context_init(&ctx, sbv_bf_realloc, NULL);"
  , "  " ++ p ++ "_decode(&ctx, &x, a); " ++ p ++ "_decode(&ctx, &y, b); bf_init(&ctx, &r);"
  , "  if (op == 0) bf_add(&r, &x, &y, " ++ show sb ++ ", " ++ p ++ "_flags(rnd));"
  , "  else if (op == 1) bf_sub(&r, &x, &y, " ++ show sb ++ ", " ++ p ++ "_flags(rnd));"
  , "  else if (op == 2) bf_mul(&r, &x, &y, " ++ show sb ++ ", " ++ p ++ "_flags(rnd));"
  , "  else if (op == 3) bf_div(&r, &x, &y, " ++ show sb ++ ", " ++ p ++ "_flags(rnd));"
  , "  else bf_rem(&r, &x, &y, " ++ show sb ++ ", " ++ p ++ "_flags(BF_RNDN), BF_RNDN);"
  , "  raw = " ++ p ++ "_encode(&r);"
  , "  bf_delete(&r); bf_delete(&y); bf_delete(&x); bf_context_end(&ctx);"
  , "  return raw;"
  , "}"
  , ""
  ]
  ++ concatMap binaryWrapper [("add", 0), ("sub", 1), ("mul", 2), ("div", 3)]
  ++ ["static inline " ++ ty ++ " " ++ p ++ "_rem(" ++ ty ++ " a, " ++ ty ++ " b)"
     , "{ return " ++ p ++ "_binary(a, b, BF_RNDN, 4); }"
     , ""
     , "static inline " ++ ty ++ " " ++ p ++ "_sqrt(" ++ ty ++ " a, bf_rnd_t rnd)"
     , "{"
     , "  bf_context_t ctx; bf_t x, r; " ++ ty ++ " raw;"
     , "  bf_context_init(&ctx, sbv_bf_realloc, NULL); " ++ p ++ "_decode(&ctx, &x, a); bf_init(&ctx, &r);"
     , "  bf_sqrt(&r, &x, " ++ show sb ++ ", " ++ p ++ "_flags(rnd)); raw = " ++ p ++ "_encode(&r);"
     , "  bf_delete(&r); bf_delete(&x); bf_context_end(&ctx); return raw;"
     , "}"
     , ""
     , "static inline " ++ ty ++ " " ++ p ++ "_round(" ++ ty ++ " a, bf_rnd_t rnd)"
     , "{"
     , "  bf_context_t ctx; bf_t x; " ++ ty ++ " raw;"
     , "  bf_context_init(&ctx, sbv_bf_realloc, NULL); " ++ p ++ "_decode(&ctx, &x, a);"
     , "  bf_rint(&x, rnd); raw = " ++ p ++ "_encode(&x);"
     , "  bf_delete(&x); bf_context_end(&ctx); return raw;"
     , "}"
     , ""
     , "static inline " ++ ty ++ " " ++ p ++ "_fma(" ++ ty ++ " a, " ++ ty ++ " b, " ++ ty ++ " c, bf_rnd_t rnd)"
     , "{"
     , "  bf_context_t ctx; bf_t x, y, z, r; " ++ ty ++ " raw;"
     , "  bf_context_init(&ctx, sbv_bf_realloc, NULL);"
     , "  " ++ p ++ "_decode(&ctx, &x, a); " ++ p ++ "_decode(&ctx, &y, b); " ++ p ++ "_decode(&ctx, &z, c); bf_init(&ctx, &r);"
     , "  bf_mul(&r, &x, &y, BF_PREC_INF, BF_RNDN); bf_add(&r, &r, &z, " ++ show sb ++ ", " ++ p ++ "_flags(rnd));"
     , "  raw = " ++ p ++ "_encode(&r);"
     , "  bf_delete(&r); bf_delete(&z); bf_delete(&y); bf_delete(&x); bf_context_end(&ctx); return raw;"
     , "}"
     , ""
     , "static inline int " ++ p ++ "_compare(" ++ ty ++ " a, " ++ ty ++ " b)"
     , "{"
     , "  bf_context_t ctx; bf_t x, y; int result;"
     , "  bf_context_init(&ctx, sbv_bf_realloc, NULL); " ++ p ++ "_decode(&ctx, &x, a); " ++ p ++ "_decode(&ctx, &y, b);"
     , "  result = bf_cmp(&x, &y); bf_delete(&y); bf_delete(&x); bf_context_end(&ctx); return result;"
     , "}"
     , ""
     , "static inline bool " ++ p ++ "_eq(" ++ ty ++ " a, " ++ ty ++ " b)"
     , "{ return " ++ p ++ "_compare(a, b) == 0; }"
     , ""
     , "static inline bool " ++ p ++ "_lt(" ++ ty ++ " a, " ++ ty ++ " b)"
     , "{ return " ++ p ++ "_compare(a, b) < 0; }"
     , ""
     , "static inline bool " ++ p ++ "_le(" ++ ty ++ " a, " ++ ty ++ " b)"
     , "{ return " ++ p ++ "_compare(a, b) <= 0; }"
     , ""
     , "static inline " ++ ty ++ " " ++ p ++ "_min(" ++ ty ++ " a, " ++ ty ++ " b)"
     , "{"
     , "  if (" ++ p ++ "_is_nan(a)) return b; if (" ++ p ++ "_is_nan(b)) return a;"
     , "  if (" ++ p ++ "_is_zero(a) && " ++ p ++ "_is_zero(b)) return " ++ p ++ "_zero();"
     , "  return " ++ p ++ "_lt(a, b) ? a : b;"
     , "}"
     , ""
     , "static inline " ++ ty ++ " " ++ p ++ "_max(" ++ ty ++ " a, " ++ ty ++ " b)"
     , "{"
     , "  if (" ++ p ++ "_is_nan(a)) return b; if (" ++ p ++ "_is_nan(b)) return a;"
     , "  if (" ++ p ++ "_is_zero(a) && " ++ p ++ "_is_zero(b)) return " ++ p ++ "_zero();"
     , "  return " ++ p ++ "_lt(b, a) ? a : b;"
     , "}"
     , ""
     ]
 where ty = arbitraryFPCType k
       p  = prefix k

       binaryWrapper :: (String, Int) -> [String]
       binaryWrapper (nm, op) =
         ["static inline " ++ ty ++ " " ++ p ++ "_" ++ nm ++ "(" ++ ty ++ " a, " ++ ty ++ " b, bf_rnd_t rnd)"
         , "{ return " ++ p ++ "_binary(a, b, rnd, " ++ show op ++ "); }"
         , ""]
arithmeticRuntime k = error $ "SBV->C: Expected an arbitrary floating-point kind, received " ++ show k

-- | Render the LibBF rounding mode corresponding to an SBV value.
bfRoundingMode :: [(SV, CV)] -> SV -> Doc
bfRoundingMode consts sv = case sv `lookup` consts of
  Just (CV k (CADT (rmName, [])))
    | isRoundingMode k -> maybe bad (text . snd) (lookup rmName roundingModeNames)
  Nothing
    | isRoundingMode sv -> namedCall "sbv_bf_rounding_mode" [text (show sv)]
  _                     -> bad
 where bad = error $ "SBV->C: Expected a rounding mode, received " ++ show sv

-- | Mapping from SBV constructor names to public C and LibBF constants.
roundingModeNames :: [(String, (String, String))]
roundingModeNames =
  [ ("RoundNearestTiesToEven", ("SBV_RM_RNE", "BF_RNDN"))
  , ("RoundNearestTiesToAway", ("SBV_RM_RNA", "BF_RNDNA"))
  , ("RoundTowardPositive",    ("SBV_RM_RTP", "BF_RNDU"))
  , ("RoundTowardNegative",    ("SBV_RM_RTN", "BF_RNDD"))
  , ("RoundTowardZero",        ("SBV_RM_RTZ", "BF_RNDZ"))
  ]

-- | Render a C function call.
namedCall :: String -> [Doc] -> Doc
namedCall nm args = text nm P.<> parens (fsep (punctuate comma args))

-- | Return the number of raw 64-bit limbs occupied by an arbitrary float.
limbs :: Kind -> Int
limbs k = (intSizeOf k + 63) `div` 64

-- | Return the mask for the high raw limb of an arbitrary float.
topMask :: Kind -> Integer
topMask k
  | r == 0    = (1 `shiftL` 64) - 1
  | otherwise = (1 `shiftL` r) - 1
 where r = intSizeOf k `mod` 64

-- | Return the generated namespace prefix for a floating-point format.
prefix :: Kind -> String
prefix (KFP eb sb) = "sbv_fp_e" ++ show eb ++ "_s" ++ show sb
prefix k           = error $ "SBV->C: Expected an arbitrary floating-point kind, received " ++ show k

-- | Render raw interchange bits as a C compound literal.
rawLiteral :: Kind -> Integer -> String
rawLiteral k bits = "(" ++ arbitraryFPCType k ++ "){{" ++ intercalate ", " words64 ++ "}}"
 where words64 = [u64 ((bits `shiftR` (64 * i)) .&. ((1 `shiftL` 64) - 1)) | i <- [0 .. limbs k - 1]]

-- | Render an integer as a padded, portable C @uint64_t@ literal.
u64 :: Integer -> String
u64 i = "UINT64_C(0x" ++ pad 16 (showHex i "") ++ ")"
 where pad n s = replicate (n - length s) '0' ++ s
