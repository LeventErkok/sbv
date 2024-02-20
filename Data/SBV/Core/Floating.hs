-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Core.Floating
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Implementation of floating-point operations mapping to SMT-Lib2 floats
-----------------------------------------------------------------------------

{-# LANGUAGE DefaultSignatures    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans -Wno-incomplete-uni-patterns #-}

module Data.SBV.Core.Floating (
         IEEEFloating(..), IEEEFloatConvertible(..)
       , sFloatAsSWord32, sDoubleAsSWord64, sFloatingPointAsSWord
       , sWord32AsSFloat, sWord64AsSDouble, sWordAsSFloatingPoint
       , blastSFloat, blastSDouble,  blastSFloatingPoint
       , sFloatAsComparableSWord32,  sDoubleAsComparableSWord64,  sFloatingPointAsComparableSWord
       , sComparableSWord32AsSFloat, sComparableSWord64AsSDouble, sComparableSWordAsSFloatingPoint
       , svFloatingPointAsSWord
       ) where

import Data.Bits (testBit)
import Data.Int  (Int8,  Int16,  Int32,  Int64)
import Data.Word (Word8, Word16, Word32, Word64)

import Data.Proxy

import Data.SBV.Core.AlgReals (isExactRational)
import Data.SBV.Core.Sized
import Data.SBV.Core.SizedFloats

import Data.SBV.Core.Data
import Data.SBV.Core.Kind
import Data.SBV.Core.Model
import Data.SBV.Core.Symbolic (addSValOptGoal)

import Data.SBV.Utils.Numeric

import Data.Ratio

import GHC.TypeLits

import LibBF

import Data.SBV.Core.Operations

-- | A class of floating-point (IEEE754) operations, some of
-- which behave differently based on rounding modes. Note that unless
-- the rounding mode is concretely RoundNearestTiesToEven, we will
-- not concretely evaluate these, but rather pass down to the SMT solver.
class (SymVal a, RealFloat a) => IEEEFloating a where
  -- | Compute the floating point absolute value.
  fpAbs             ::                  SBV a -> SBV a

  -- | Compute the unary negation. Note that @0 - x@ is not equivalent to @-x@ for floating-point, since @-0@ and @0@ are different.
  fpNeg             ::                  SBV a -> SBV a

  -- | Add two floating point values, using the given rounding mode
  fpAdd             :: SRoundingMode -> SBV a -> SBV a -> SBV a

  -- | Subtract two floating point values, using the given rounding mode
  fpSub             :: SRoundingMode -> SBV a -> SBV a -> SBV a

  -- | Multiply two floating point values, using the given rounding mode
  fpMul             :: SRoundingMode -> SBV a -> SBV a -> SBV a

  -- | Divide two floating point values, using the given rounding mode
  fpDiv             :: SRoundingMode -> SBV a -> SBV a -> SBV a

  -- | Fused-multiply-add three floating point values, using the given rounding mode. @fpFMA x y z = x*y+z@ but with only
  -- one rounding done for the whole operation; not two. Note that we will never concretely evaluate this function since
  -- Haskell lacks an FMA implementation.
  fpFMA             :: SRoundingMode -> SBV a -> SBV a -> SBV a -> SBV a

  -- | Compute the square-root of a float, using the given rounding mode
  fpSqrt            :: SRoundingMode -> SBV a -> SBV a

  -- | Compute the remainder: @x - y * n@, where @n@ is the truncated integer nearest to x/y. The rounding mode
  -- is implicitly assumed to be @RoundNearestTiesToEven@.
  fpRem             ::                  SBV a -> SBV a -> SBV a

  -- | Round to the nearest integral value, using the given rounding mode.
  fpRoundToIntegral :: SRoundingMode -> SBV a -> SBV a

  -- | Compute the minimum of two floats, respects @infinity@ and @NaN@ values
  fpMin             ::                  SBV a -> SBV a -> SBV a

  -- | Compute the maximum of two floats, respects @infinity@ and @NaN@ values
  fpMax             ::                  SBV a -> SBV a -> SBV a

  -- | Are the two given floats exactly the same. That is, @NaN@ will compare equal to itself, @+0@ will /not/ compare
  -- equal to @-0@ etc. This is the object level equality, as opposed to the semantic equality. (For the latter, just use '.=='.)
  fpIsEqualObject   ::                  SBV a -> SBV a -> SBool

  -- | Is the floating-point number a normal value. (i.e., not denormalized.)
  fpIsNormal :: SBV a -> SBool

  -- | Is the floating-point number a subnormal value. (Also known as denormal.)
  fpIsSubnormal :: SBV a -> SBool

  -- | Is the floating-point number 0? (Note that both +0 and -0 will satisfy this predicate.)
  fpIsZero :: SBV a -> SBool

  -- | Is the floating-point number infinity? (Note that both +oo and -oo will satisfy this predicate.)
  fpIsInfinite :: SBV a -> SBool

  -- | Is the floating-point number a NaN value?
  fpIsNaN ::  SBV a -> SBool

  -- | Is the floating-point number negative? Note that -0 satisfies this predicate but +0 does not.
  fpIsNegative :: SBV a -> SBool

  -- | Is the floating-point number positive? Note that +0 satisfies this predicate but -0 does not.
  fpIsPositive :: SBV a -> SBool

  -- | Is the floating point number -0?
  fpIsNegativeZero :: SBV a -> SBool

  -- | Is the floating point number +0?
  fpIsPositiveZero :: SBV a -> SBool

  -- | Is the floating-point number a regular floating point, i.e., not NaN, nor +oo, nor -oo. Normals or denormals are allowed.
  fpIsPoint :: SBV a -> SBool

  -- Default definitions. Minimal complete definition: None! All should be taken care by defaults
  -- Note that we never evaluate FMA concretely, as there's no fma operator in Haskell
  fpAbs              = lift1  FP_Abs             (Just abs)                Nothing
  fpNeg              = lift1  FP_Neg             (Just negate)             Nothing
  fpAdd              = lift2  FP_Add             (Just (+))                . Just
  fpSub              = lift2  FP_Sub             (Just (-))                . Just
  fpMul              = lift2  FP_Mul             (Just (*))                . Just
  fpDiv              = lift2  FP_Div             (Just (/))                . Just
  fpFMA              = lift3  FP_FMA             Nothing                   . Just
  fpSqrt             = lift1  FP_Sqrt            (Just sqrt)               . Just
  fpRem              = lift2  FP_Rem             (Just fpRemH)             Nothing
  fpRoundToIntegral  = lift1  FP_RoundToIntegral (Just fpRoundToIntegralH) . Just
  fpMin              = liftMM FP_Min             (Just fpMinH)             Nothing
  fpMax              = liftMM FP_Max             (Just fpMaxH)             Nothing
  fpIsEqualObject    = lift2B FP_ObjEqual        (Just fpIsEqualObjectH)   Nothing
  fpIsNormal         = lift1B FP_IsNormal        fpIsNormalizedH
  fpIsSubnormal      = lift1B FP_IsSubnormal     isDenormalized
  fpIsZero           = lift1B FP_IsZero          (== 0)
  fpIsInfinite       = lift1B FP_IsInfinite      isInfinite
  fpIsNaN            = lift1B FP_IsNaN           isNaN
  fpIsNegative       = lift1B FP_IsNegative      (\x -> x < 0 ||       isNegativeZero x)
  fpIsPositive       = lift1B FP_IsPositive      (\x -> x >= 0 && not (isNegativeZero x))
  fpIsNegativeZero x = fpIsZero x .&& fpIsNegative x
  fpIsPositiveZero x = fpIsZero x .&& fpIsPositive x
  fpIsPoint        x = sNot (fpIsNaN x .|| fpIsInfinite x)

-- | SFloat instance
instance IEEEFloating Float

-- | SDouble instance
instance IEEEFloating Double

-- | Conversion to and from floats
class SymVal a => IEEEFloatConvertible a where
  -- | Convert from an IEEE74 single precision float.
  fromSFloat :: SRoundingMode -> SFloat -> SBV a
  fromSFloat = genericFromFloat

  -- | Convert to an IEEE-754 Single-precision float.
  toSFloat :: SRoundingMode -> SBV a -> SFloat

  -- default definition if we have an integral like
  default toSFloat :: Integral a => SRoundingMode -> SBV a -> SFloat
  toSFloat = genericToFloat (onlyWhenRNE (Just . fromRational . fromIntegral))

  -- | Convert from an IEEE74 double precision float.
  fromSDouble :: SRoundingMode -> SDouble -> SBV a
  fromSDouble = genericFromFloat

  -- | Convert to an IEEE-754 Double-precision float.
  toSDouble :: SRoundingMode -> SBV a -> SDouble

  -- default definition if we have an integral like
  default toSDouble :: Integral a => SRoundingMode -> SBV a -> SDouble
  toSDouble = genericToFloat (onlyWhenRNE (Just . fromRational . fromIntegral))

  -- | Convert from an arbitrary floating point.
  fromSFloatingPoint :: ValidFloat eb sb => SRoundingMode -> SFloatingPoint eb sb -> SBV a
  fromSFloatingPoint = genericFromFloat

  -- | Convert to an arbitrary floating point.
  toSFloatingPoint :: ValidFloat eb sb => SRoundingMode -> SBV a -> SFloatingPoint eb sb

  -- -- default definition if we have an integral like
  default toSFloatingPoint :: (Integral a, ValidFloat eb sb) => SRoundingMode -> SBV a -> SFloatingPoint eb sb
  toSFloatingPoint = genericToFloat (const (Just . fromRational . fromIntegral))

-- Run the function if the conversion is in RNE. Otherwise return Nothing.
onlyWhenRNE :: (a -> Maybe b) -> RoundingMode -> a -> Maybe b
onlyWhenRNE f RoundNearestTiesToEven v = f v
onlyWhenRNE _ _                      _ = Nothing

-- | A generic from-float converter. Note that this function does no constant folding since
-- it's behavior is undefined when the input float is out-of-bounds or not a point.
genericFromFloat :: forall a r. (IEEEFloating a, IEEEFloatConvertible r)
                 => SRoundingMode            -- Rounding mode
                 -> SBV a                    -- Input float/double
                 -> SBV r
genericFromFloat rm f = SBV (SVal kTo (Right (cache r)))
  where kFrom = kindOf f
        kTo   = kindOf (Proxy @r)
        r st  = do msv <- sbvToSV st rm
                   xsv <- sbvToSV st f
                   newExpr st kTo (SBVApp (IEEEFP (FP_Cast kFrom kTo msv)) [xsv])

-- | A generic to-float converter, which will constant-fold as necessary, but only in the sRNE mode for regular floats.
genericToFloat :: forall a r. (IEEEFloatConvertible a, IEEEFloating r)
               => (RoundingMode -> a -> Maybe r)     -- How to convert concretely, if possible
               -> SRoundingMode                      -- Rounding mode
               -> SBV a                              -- Input convertible
               -> SBV r
genericToFloat converter rm i
  | Just w <- unliteral i, Just crm <- unliteral rm, Just result <- converter crm w
  = literal result
  | True
  = SBV (SVal kTo (Right (cache r)))
  where kFrom = kindOf i
        kTo   = kindOf (Proxy @r)
        r st  = do msv <- sbvToSV st rm
                   xsv <- sbvToSV st i
                   newExpr st kTo (SBVApp (IEEEFP (FP_Cast kFrom kTo msv)) [xsv])

instance IEEEFloatConvertible Int8
instance IEEEFloatConvertible Int16
instance IEEEFloatConvertible Int32
instance IEEEFloatConvertible Int64
instance IEEEFloatConvertible Word8
instance IEEEFloatConvertible Word16
instance IEEEFloatConvertible Word32
instance IEEEFloatConvertible Word64
instance IEEEFloatConvertible Integer

-- For float and double, skip the conversion if the same and do the constant folding, unlike all others.
instance IEEEFloatConvertible Float where
  toSFloat  _ f = f
  toSDouble     = genericToFloat (onlyWhenRNE (Just . fp2fp))

  toSFloatingPoint rm f = toSFloatingPoint rm $ toSDouble rm f

  fromSFloat  _  f = f
  fromSDouble rm f
    | Just RoundNearestTiesToEven <- unliteral rm
    , Just fv                     <- unliteral f
    = literal (fp2fp fv)
    | True
    = genericFromFloat rm f

instance IEEEFloatConvertible Double where
  toSFloat      = genericToFloat (onlyWhenRNE (Just . fp2fp))
  toSDouble _ d = d

  toSFloatingPoint rm sd
    | Just d <- unliteral sd, Just brm <- rmToRM rm
    = literal $ FloatingPoint $ FP ei si $ fst (bfRoundFloat (mkBFOpts ei si brm) (bfFromDouble d))
    | True
    = res
    where (k, ei, si) = case kindOf res of
                         kr@(KFP eb sb) -> (kr, eb, sb)
                         kr             -> error $ "Unexpected kind in toSFloatingPoint: " ++ show (kr, rm, sd)
          res = SBV $ SVal k $ Right $ cache r
          r st = do msv <- sbvToSV st rm
                    xsv <- sbvToSV st sd
                    newExpr st k (SBVApp (IEEEFP (FP_Cast KDouble k msv)) [xsv])

  fromSDouble _  d = d
  fromSFloat  rm d
    | Just RoundNearestTiesToEven <- unliteral rm
    , Just dv                     <- unliteral d
    = literal (fp2fp dv)
    | True
    = genericFromFloat rm d

convertWhenExactRational :: Fractional a => AlgReal -> Maybe a
convertWhenExactRational r
  | isExactRational r = Just (fromRational (toRational r))
  | True              = Nothing

-- For AlgReal; be careful to only process exact rationals concretely
instance IEEEFloatConvertible AlgReal where
  toSFloat         = genericToFloat (onlyWhenRNE convertWhenExactRational)
  toSDouble        = genericToFloat (onlyWhenRNE convertWhenExactRational)
  toSFloatingPoint = genericToFloat (const       convertWhenExactRational)

-- Arbitrary floats can handle all rounding modes in concrete mode
instance ValidFloat eb sb => IEEEFloatConvertible (FloatingPoint eb sb) where
  toSFloat rm i
    | Just (FloatingPoint (FP _ _ v)) <- unliteral i, Just brm <- rmToRM rm
    = literal $ fp2fp $ fst (bfToDouble brm (fst (bfRoundFloat (mkBFOpts ei si brm) v)))
    | True
    = genericToFloat (\_ _ -> Nothing) rm i
    where ei = intOfProxy (Proxy @eb)
          si = intOfProxy (Proxy @sb)

  fromSFloat rm i
    | Just f <- unliteral i, Just brm <- rmToRM rm
    = literal $ FloatingPoint $ FP ei si $ fst (bfRoundFloat (mkBFOpts ei si brm) (bfFromDouble (fp2fp f :: Double)))
    | True
    = genericFromFloat rm i
    where ei = intOfProxy (Proxy @eb)
          si = intOfProxy (Proxy @sb)

  toSDouble rm i
    | Just (FloatingPoint (FP _ _ v)) <- unliteral i, Just brm <- rmToRM rm
    = literal $ fst (bfToDouble brm (fst (bfRoundFloat (mkBFOpts ei si brm) v)))
    | True
    = genericToFloat (\_ _ -> Nothing) rm i
    where ei = intOfProxy (Proxy @eb)
          si = intOfProxy (Proxy @sb)

  fromSDouble rm i
    | Just f <- unliteral i, Just brm <- rmToRM rm
    = literal $ FloatingPoint $ FP ei si $ fst (bfRoundFloat (mkBFOpts ei si brm) (bfFromDouble f))
    | True
    = genericFromFloat rm i
    where ei = intOfProxy (Proxy @eb)
          si = intOfProxy (Proxy @sb)

  toSFloatingPoint rm i
    | Just (FloatingPoint (FP _ _ v)) <- unliteral i, Just brm <- rmToRM rm
    = literal $ FloatingPoint $ FP ei si $ fst (bfRoundFloat (mkBFOpts ei si brm) v)
    | True
    = genericToFloat (\_ _ -> Nothing) rm i
    where ei = intOfProxy (Proxy @eb)
          si = intOfProxy (Proxy @sb)

  -- From and To are the same when the source is an arbitrary float!
  fromSFloatingPoint = toSFloatingPoint

-- | Concretely evaluate one arg function, if rounding mode is RoundNearestTiesToEven and we have enough concrete data
concEval1 :: SymVal a => Maybe (a -> a) -> Maybe SRoundingMode -> SBV a -> Maybe (SBV a)
concEval1 mbOp mbRm a = do op <- mbOp
                           v  <- unliteral a
                           case unliteral =<< mbRm of
                                   Nothing                     -> (Just . literal) (op v)
                                   Just RoundNearestTiesToEven -> (Just . literal) (op v)
                                   _                           -> Nothing

-- | Concretely evaluate two arg function, if rounding mode is RoundNearestTiesToEven and we have enough concrete data
concEval2 :: SymVal a => Maybe (a -> a -> a) -> Maybe SRoundingMode -> SBV a -> SBV a -> Maybe (SBV a)
concEval2 mbOp mbRm a b = do op <- mbOp
                             v1 <- unliteral a
                             v2 <- unliteral b
                             case unliteral =<< mbRm of
                                     Nothing                     -> (Just . literal) (v1 `op` v2)
                                     Just RoundNearestTiesToEven -> (Just . literal) (v1 `op` v2)
                                     _                           -> Nothing

-- | Concretely evaluate a bool producing two arg function, if rounding mode is RoundNearestTiesToEven and we have enough concrete data
concEval2B :: SymVal a => Maybe (a -> a -> Bool) -> Maybe SRoundingMode -> SBV a -> SBV a -> Maybe SBool
concEval2B mbOp mbRm a b = do op <- mbOp
                              v1 <- unliteral a
                              v2 <- unliteral b
                              case unliteral =<< mbRm of
                                      Nothing                     -> (Just . literal) (v1 `op` v2)
                                      Just RoundNearestTiesToEven -> (Just . literal) (v1 `op` v2)
                                      _                           -> Nothing

-- | Concretely evaluate two arg function, if rounding mode is RoundNearestTiesToEven and we have enough concrete data
concEval3 :: SymVal a => Maybe (a -> a -> a -> a) -> Maybe SRoundingMode -> SBV a -> SBV a -> SBV a -> Maybe (SBV a)
concEval3 mbOp mbRm a b c = do op <- mbOp
                               v1 <- unliteral a
                               v2 <- unliteral b
                               v3 <- unliteral c
                               case unliteral =<< mbRm of
                                       Nothing                     -> (Just . literal) (op v1 v2 v3)
                                       Just RoundNearestTiesToEven -> (Just . literal) (op v1 v2 v3)
                                       _                           -> Nothing

-- | Add the converted rounding mode if given as an argument
addRM :: State -> Maybe SRoundingMode -> [SV] -> IO [SV]
addRM _  Nothing   as = return as
addRM st (Just rm) as = do svm <- sbvToSV st rm
                           return (svm : as)

-- | Lift a 1 arg FP-op
lift1 :: SymVal a => FPOp -> Maybe (a -> a) -> Maybe SRoundingMode -> SBV a -> SBV a
lift1 w mbOp mbRm a
  | Just cv <- concEval1 mbOp mbRm a
  = cv
  | True
  = SBV $ SVal k $ Right $ cache r
  where k    = kindOf a
        r st = do sva  <- sbvToSV st a
                  args <- addRM st mbRm [sva]
                  newExpr st k (SBVApp (IEEEFP w) args)

-- | Lift an FP predicate
lift1B :: SymVal a => FPOp -> (a -> Bool) -> SBV a -> SBool
lift1B w f a
   | Just v <- unliteral a = literal $ f v
   | True                  = SBV $ SVal KBool $ Right $ cache r
   where r st = do sva <- sbvToSV st a
                   newExpr st KBool (SBVApp (IEEEFP w) [sva])


-- | Lift a 2 arg FP-op
lift2 :: SymVal a => FPOp -> Maybe (a -> a -> a) -> Maybe SRoundingMode -> SBV a -> SBV a -> SBV a
lift2 w mbOp mbRm a b
  | Just cv <- concEval2 mbOp mbRm a b
  = cv
  | True
  = SBV $ SVal k $ Right $ cache r
  where k    = kindOf a
        r st = do sva  <- sbvToSV st a
                  svb  <- sbvToSV st b
                  args <- addRM st mbRm [sva, svb]
                  newExpr st k (SBVApp (IEEEFP w) args)

-- | Lift min/max: Note that we protect against constant folding if args are alternating sign 0's, since
-- SMTLib is deliberately nondeterministic in this case
liftMM :: (SymVal a, RealFloat a) => FPOp -> Maybe (a -> a -> a) -> Maybe SRoundingMode -> SBV a -> SBV a -> SBV a
liftMM w mbOp mbRm a b
  | Just v1 <- unliteral a
  , Just v2 <- unliteral b
  , not ((isN0 v1 && isP0 v2) || (isP0 v1 && isN0 v2))          -- If not +0/-0 or -0/+0
  , Just cv <- concEval2 mbOp mbRm a b
  = cv
  | True
  = SBV $ SVal k $ Right $ cache r
  where isN0   = isNegativeZero
        isP0 x = x == 0 && not (isN0 x)
        k    = kindOf a
        r st = do sva  <- sbvToSV st a
                  svb  <- sbvToSV st b
                  args <- addRM st mbRm [sva, svb]
                  newExpr st k (SBVApp (IEEEFP w) args)

-- | Lift a 2 arg FP-op, producing bool
lift2B :: SymVal a => FPOp -> Maybe (a -> a -> Bool) -> Maybe SRoundingMode -> SBV a -> SBV a -> SBool
lift2B w mbOp mbRm a b
  | Just cv <- concEval2B mbOp mbRm a b
  = cv
  | True
  = SBV $ SVal KBool $ Right $ cache r
  where r st = do sva  <- sbvToSV st a
                  svb  <- sbvToSV st b
                  args <- addRM st mbRm [sva, svb]
                  newExpr st KBool (SBVApp (IEEEFP w) args)

-- | Lift a 3 arg FP-op
lift3 :: SymVal a => FPOp -> Maybe (a -> a -> a -> a) -> Maybe SRoundingMode -> SBV a -> SBV a -> SBV a -> SBV a
lift3 w mbOp mbRm a b c
  | Just cv <- concEval3 mbOp mbRm a b c
  = cv
  | True
  = SBV $ SVal k $ Right $ cache r
  where k    = kindOf a
        r st = do sva  <- sbvToSV st a
                  svb  <- sbvToSV st b
                  svc  <- sbvToSV st c
                  args <- addRM st mbRm [sva, svb, svc]
                  newExpr st k (SBVApp (IEEEFP w) args)

-- | Convert an 'SFloat' to an 'SWord32', preserving the bit-correspondence. Note that since the
-- representation for @NaN@s are not unique, this function will return a symbolic value when given a
-- concrete @NaN@.
--
-- Implementation note: Since there's no corresponding function in SMTLib for conversion to
-- bit-representation due to partiality, we use a translation trick by allocating a new word variable,
-- converting it to float, and requiring it to be equivalent to the input. In code-generation mode, we simply map
-- it to a simple conversion.
sFloatAsSWord32 :: SFloat -> SWord32
sFloatAsSWord32 (SBV v) = SBV $ svFloatAsSWord32 v

-- | Convert an 'SDouble' to an 'SWord64', preserving the bit-correspondence. Note that since the
-- representation for @NaN@s are not unique, this function will return a symbolic value when given a
-- concrete @NaN@.
--
-- See the implementation note for 'sFloatAsSWord32', as it applies here as well.
sDoubleAsSWord64 :: SDouble -> SWord64
sDoubleAsSWord64 (SBV v) = SBV $ svDoubleAsSWord64 v

-- | Extract the sign\/exponent\/mantissa of a single-precision float. The output will have
-- 8 bits in the second argument for exponent, and 23 in the third for the mantissa.
blastSFloat :: SFloat -> (SBool, [SBool], [SBool])
blastSFloat = extract . sFloatAsSWord32
 where extract x = (sTestBit x 31, sExtractBits x [30, 29 .. 23], sExtractBits x [22, 21 .. 0])

-- | Extract the sign\/exponent\/mantissa of a single-precision float. The output will have
-- 11 bits in the second argument for exponent, and 52 in the third for the mantissa.
blastSDouble :: SDouble -> (SBool, [SBool], [SBool])
blastSDouble = extract . sDoubleAsSWord64
 where extract x = (sTestBit x 63, sExtractBits x [62, 61 .. 52], sExtractBits x [51, 50 .. 0])

-- | Extract the sign\/exponent\/mantissa of an arbitrary precision float. The output will have
-- @eb@ bits in the second argument for exponent, and @sb-1@ bits in the third for mantissa.
blastSFloatingPoint :: forall eb sb. (ValidFloat eb sb, KnownNat (eb + sb), BVIsNonZero (eb + sb))
                    => SFloatingPoint eb sb -> (SBool, [SBool], [SBool])
blastSFloatingPoint = extract . sFloatingPointAsSWord
  where ei = intOfProxy (Proxy @eb)
        si = intOfProxy (Proxy @sb)
        extract x = (sTestBit x (ei + si - 1), sExtractBits x [ei + si - 2, ei + si - 3 .. si - 1], sExtractBits x [si - 2, si - 3 .. 0])

-- | Reinterpret the bits in a 32-bit word as a single-precision floating point number
sWord32AsSFloat :: SWord32 -> SFloat
sWord32AsSFloat fVal
  | Just f <- unliteral fVal = literal $ wordToFloat f
  | True                     = SBV (SVal KFloat (Right (cache y)))
  where y st = do xsv <- sbvToSV st fVal
                  newExpr st KFloat (SBVApp (IEEEFP (FP_Reinterpret (kindOf fVal) KFloat)) [xsv])

-- | Reinterpret the bits in a 32-bit word as a single-precision floating point number
sWord64AsSDouble :: SWord64 -> SDouble
sWord64AsSDouble dVal
  | Just d <- unliteral dVal = literal $ wordToDouble d
  | True                     = SBV (SVal KDouble (Right (cache y)))
  where y st = do xsv <- sbvToSV st dVal
                  newExpr st KDouble (SBVApp (IEEEFP (FP_Reinterpret (kindOf dVal) KDouble)) [xsv])

-- | Convert a float to a comparable 'SWord32'. The trick is to ignore the
-- sign of -0, and if it's a negative value flip all the bits, and otherwise
-- only flip the sign bit. This is known as the lexicographic ordering on floats
-- and it works as long as you do not have a @NaN@.
sFloatAsComparableSWord32 :: SFloat -> SWord32
sFloatAsComparableSWord32 f = ite (fpIsNegativeZero f) (sFloatAsComparableSWord32 0) (fromBitsBE $ sNot sb : ite sb (map sNot rest) rest)
  where (sb : rest) = blastBE $ sFloatAsSWord32 f

-- | Inverse transformation to 'sFloatAsComparableSWord32'.
sComparableSWord32AsSFloat :: SWord32 -> SFloat
sComparableSWord32AsSFloat w = sWord32AsSFloat $ ite sb (fromBitsBE $ sFalse : rest) (fromBitsBE $ map sNot allBits)
  where allBits@(sb : rest) = blastBE w

-- | Convert a double to a comparable 'SWord64'. The trick is to ignore the
-- sign of -0, and if it's a negative value flip all the bits, and otherwise
-- only flip the sign bit. This is known as the lexicographic ordering on doubles
-- and it works as long as you do not have a @NaN@.
sDoubleAsComparableSWord64 :: SDouble -> SWord64
sDoubleAsComparableSWord64 d = ite (fpIsNegativeZero d) (sDoubleAsComparableSWord64 0) (fromBitsBE $ sNot sb : ite sb (map sNot rest) rest)
  where (sb : rest) = blastBE $ sDoubleAsSWord64 d

-- | Inverse transformation to 'sDoubleAsComparableSWord64'. Note that this isn't a perfect inverse, since @-0@ maps to @0@ and back to @0@.
-- Otherwise, it's faithful:
sComparableSWord64AsSDouble :: SWord64 -> SDouble
sComparableSWord64AsSDouble w = sWord64AsSDouble $ ite sb (fromBitsBE $ sFalse : rest) (fromBitsBE $ map sNot allBits)
  where allBits@(sb : rest) = blastBE w

-- | 'Float' instance for 'Metric' goes through the lexicographic ordering on 'Word32'.
-- It implicitly makes sure that the value is not @NaN@.
instance Metric Float where

   type MetricSpace Float = Word32
   toMetricSpace          = sFloatAsComparableSWord32
   fromMetricSpace        = sComparableSWord32AsSFloat

   msMinimize nm o = do constrain $ sNot $ fpIsNaN o
                        addSValOptGoal $ unSBV `fmap` Minimize nm (toMetricSpace o)

   msMaximize nm o = do constrain $ sNot $ fpIsNaN o
                        addSValOptGoal $ unSBV `fmap` Maximize nm (toMetricSpace o)

-- | 'Double' instance for 'Metric' goes through the lexicographic ordering on 'Word64'.
-- It implicitly makes sure that the value is not @NaN@.
instance Metric Double where

   type MetricSpace Double = Word64
   toMetricSpace           = sDoubleAsComparableSWord64
   fromMetricSpace         = sComparableSWord64AsSDouble

   msMinimize nm o = do constrain $ sNot $ fpIsNaN o
                        addSValOptGoal $ unSBV `fmap` Minimize nm (toMetricSpace o)

   msMaximize nm o = do constrain $ sNot $ fpIsNaN o
                        addSValOptGoal $ unSBV `fmap` Maximize nm (toMetricSpace o)

-- | Real instance for FloatingPoint. NB. The methods haven't been subjected to much testing, so beware of any floating-point snafus here.
instance ValidFloat eb sb => Real (FloatingPoint eb sb) where
  toRational (FloatingPoint (FP _ _ r)) = case bfToRep r of
                                            BFNaN     -> toRational (0/0 :: Double)
                                            BFRep s n -> case n of
                                                           Zero    -> 0 % 1
                                                           Inf     -> (if s == Neg then -1 else 1) % 0
                                                           Num x y -> -- The value here is x * 2^y
                                                                      let v :: Integer
                                                                          v   = 2 ^ abs (fromIntegral y :: Integer)
                                                                          sgn = if s == Neg then ((-1) *) else id
                                                                      in if y > 0
                                                                            then sgn $ x * v % 1
                                                                            else sgn $ x % v

-- | RealFrac instance for FloatingPoint. NB. The methods haven't been subjected to much testing, so beware of any floating-point snafus here.
instance ValidFloat eb sb => RealFrac (FloatingPoint eb sb) where
  properFraction (FloatingPoint f) = (a, FloatingPoint b)
     where (a, b) = properFraction f

-- | RealFloat instance for FloatingPoint. NB. The methods haven't been subjected to much testing, so beware of any floating-point snafus here.
instance ValidFloat eb sb => RealFloat (FloatingPoint eb sb) where
  floatRadix     (FloatingPoint f) = floatRadix     f
  floatDigits    (FloatingPoint f) = floatDigits    f
  floatRange     (FloatingPoint f) = floatRange     f
  isNaN          (FloatingPoint f) = isNaN          f
  isInfinite     (FloatingPoint f) = isInfinite     f
  isDenormalized (FloatingPoint f) = isDenormalized f
  isNegativeZero (FloatingPoint f) = isNegativeZero f
  isIEEE         (FloatingPoint f) = isIEEE         f
  decodeFloat    (FloatingPoint f) = decodeFloat    f

  encodeFloat m n = res
     where res = FloatingPoint $ fpEncodeFloat ei si m n
           ei = intOfProxy (Proxy @eb)
           si = intOfProxy (Proxy @sb)

-- | Convert a float to the word containing the corresponding bit pattern
sFloatingPointAsSWord :: forall eb sb. (ValidFloat eb sb, KnownNat (eb + sb), BVIsNonZero (eb + sb)) => SFloatingPoint eb sb -> SWord (eb + sb)
sFloatingPointAsSWord (SBV v) = SBV (svFloatingPointAsSWord v)

-- | Convert a float to the correct size word, that can be used in lexicographic ordering. Used in optimization.
sFloatingPointAsComparableSWord :: forall eb sb. (ValidFloat eb sb, KnownNat (eb + sb), BVIsNonZero (eb + sb)) => SFloatingPoint eb sb -> SWord (eb + sb)
sFloatingPointAsComparableSWord f = ite (fpIsNegativeZero f) posZero (fromBitsBE $ sNot sb : ite sb (map sNot rest) rest)
  where posZero     = sFloatingPointAsComparableSWord (0 :: SFloatingPoint eb sb)
        (sb : rest) = blastBE (sFloatingPointAsSWord f :: SWord (eb + sb))

-- | Inverse transformation to 'sFloatingPointAsComparableSWord'. Note that this isn't a perfect inverse, since @-0@ maps to @0@ and back to @0@.
-- Otherwise, it's faithful:
sComparableSWordAsSFloatingPoint :: forall eb sb. (KnownNat (eb + sb), BVIsNonZero (eb + sb), ValidFloat eb sb) => SWord (eb + sb) -> SFloatingPoint eb sb
sComparableSWordAsSFloatingPoint w = sWordAsSFloatingPoint $ ite signBit (fromBitsBE $ sFalse : rest) (fromBitsBE $ map sNot allBits)
  where allBits@(signBit : rest) = blastBE w

-- | Convert a word to an arbitrary float, by reinterpreting the bits of the word as the corresponding bits of the float.
sWordAsSFloatingPoint :: forall eb sb. (KnownNat (eb + sb), BVIsNonZero (eb + sb), ValidFloat eb sb) => SWord (eb + sb) -> SFloatingPoint eb sb
sWordAsSFloatingPoint sw
   | Just (f :: WordN (eb + sb)) <- unliteral sw
   = let ext i = f `testBit` i
         exts  = map ext
         (s, ebits, sigbits) = (ext (ei + si - 1), exts [ei + si - 2, ei + si - 3 .. si - 1], exts [si - 2, si - 3 .. 0])

         cvt :: [Bool] -> Integer
         cvt = foldr (\b sofar -> 2 * sofar + if b then 1 else 0) 0 . reverse

         eIntV = cvt ebits
         sIntV = cvt sigbits
         fp    = fpFromRawRep s (eIntV, ei) (sIntV, si)
     in literal $ FloatingPoint fp
   | True
   = SBV (SVal kTo (Right (cache y)))
   where ei   = intOfProxy (Proxy @eb)
         si   = intOfProxy (Proxy @sb)
         kTo  = KFP ei si
         y st = do xsv <- sbvToSV st sw
                   newExpr st kTo (SBVApp (IEEEFP (FP_Reinterpret (kindOf sw) kTo)) [xsv])

instance (BVIsNonZero (eb + sb), KnownNat (eb + sb), ValidFloat eb sb) => Metric (FloatingPoint eb sb) where

   type MetricSpace (FloatingPoint eb sb) = WordN (eb + sb)
   toMetricSpace                          = sFloatingPointAsComparableSWord
   fromMetricSpace                        = sComparableSWordAsSFloatingPoint

   msMinimize nm o = do constrain $ sNot $ fpIsNaN o
                        addSValOptGoal $ unSBV `fmap` Minimize nm (toMetricSpace o)

   msMaximize nm o = do constrain $ sNot $ fpIsNaN o
                        addSValOptGoal $ unSBV `fmap` Maximize nm (toMetricSpace o)

-- Map SBV's rounding modes to LibBF's
rmToRM :: SRoundingMode -> Maybe RoundMode
rmToRM srm = cvt <$> unliteral srm
  where cvt RoundNearestTiesToEven = NearEven
        cvt RoundNearestTiesToAway = NearAway
        cvt RoundTowardPositive    = ToPosInf
        cvt RoundTowardNegative    = ToNegInf
        cvt RoundTowardZero        = ToZero

-- | Lift a 1 arg Big-float op
lift1FP :: forall eb sb. ValidFloat eb sb =>
           (BFOpts -> BigFloat -> (BigFloat, Status))
        -> (Maybe SRoundingMode -> SFloatingPoint eb sb -> SFloatingPoint eb sb)
        -> SRoundingMode
        -> SFloatingPoint eb sb
        -> SFloatingPoint eb sb
lift1FP bfOp mkDef rm a
  | Just (FloatingPoint (FP _ _ v)) <- unliteral a
  , Just brm <- rmToRM rm
  = literal $ FloatingPoint (FP ei si (fst (bfOp (mkBFOpts ei si brm) v)))
  | True
  = mkDef (Just rm) a
  where ei = intOfProxy (Proxy @eb)
        si = intOfProxy (Proxy @sb)

-- | Lift a 2 arg Big-float op
lift2FP :: forall eb sb. ValidFloat eb sb =>
           (BFOpts -> BigFloat -> BigFloat -> (BigFloat, Status))
        -> (Maybe SRoundingMode -> SFloatingPoint eb sb -> SFloatingPoint eb sb -> SFloatingPoint eb sb)
        -> SRoundingMode
        -> SFloatingPoint eb sb
        -> SFloatingPoint eb sb
        -> SFloatingPoint eb sb
lift2FP bfOp mkDef rm a b
  | Just (FloatingPoint (FP _ _ v1)) <- unliteral a
  , Just (FloatingPoint (FP _ _ v2)) <- unliteral b
  , Just brm <- rmToRM rm
  = literal $ FloatingPoint (FP ei si (fst (bfOp (mkBFOpts ei si brm) v1 v2)))
  | True
  = mkDef (Just rm) a b
  where ei = intOfProxy (Proxy @eb)
        si = intOfProxy (Proxy @sb)

-- | Lift a 3 arg Big-float op
lift3FP :: forall eb sb. ValidFloat eb sb =>
           (BFOpts -> BigFloat -> BigFloat -> BigFloat -> (BigFloat, Status))
        -> (Maybe SRoundingMode -> SFloatingPoint eb sb -> SFloatingPoint eb sb -> SFloatingPoint eb sb -> SFloatingPoint eb sb)
        -> SRoundingMode
        -> SFloatingPoint eb sb
        -> SFloatingPoint eb sb
        -> SFloatingPoint eb sb
        -> SFloatingPoint eb sb
lift3FP bfOp mkDef rm a b c
  | Just (FloatingPoint (FP _ _ v1)) <- unliteral a
  , Just (FloatingPoint (FP _ _ v2)) <- unliteral b
  , Just (FloatingPoint (FP _ _ v3)) <- unliteral c
  , Just brm <- rmToRM rm
  = literal $ FloatingPoint (FP ei si (fst (bfOp (mkBFOpts ei si brm) v1 v2 v3)))
  | True
  = mkDef (Just rm) a b c
  where ei = intOfProxy (Proxy @eb)
        si = intOfProxy (Proxy @sb)

-- Sized-floats have a special instance, since it can handle arbitrary rounding modes when it matters.
instance ValidFloat eb sb => IEEEFloating (FloatingPoint eb sb) where
  fpAdd  = lift2FP bfAdd      (lift2 FP_Add  (Just (+)))
  fpSub  = lift2FP bfSub      (lift2 FP_Sub  (Just (-)))
  fpMul  = lift2FP bfMul      (lift2 FP_Mul  (Just (*)))
  fpDiv  = lift2FP bfDiv      (lift2 FP_Div  (Just (/)))
  fpFMA  = lift3FP bfFMA      (lift3 FP_FMA  Nothing)
  fpSqrt = lift1FP bfSqrt     (lift1 FP_Sqrt (Just sqrt))

  fpRoundToIntegral rm a
    | Just (FloatingPoint (FP ei si v)) <- unliteral a
    , Just brm <- rmToRM rm
    = literal $ FloatingPoint (FP ei si (fst (bfRoundInt brm v)))
    | True
    = lift1 FP_RoundToIntegral (Just fpRoundToIntegralH) (Just rm) a

  -- All other operations are agnostic to the rounding mode, hence the defaults are sufficient:
  --
  --       fpAbs            :: SBV a -> SBV a
  --       fpNeg            :: SBV a -> SBV a
  --       fpRem            :: SBV a -> SBV a -> SBV a
  --       fpMin            :: SBV a -> SBV a -> SBV a
  --       fpMax            :: SBV a -> SBV a -> SBV a
  --       fpIsEqualObject  :: SBV a -> SBV a -> SBool
  --       fpIsNormal       :: SBV a -> SBool
  --       fpIsSubnormal    :: SBV a -> SBool
  --       fpIsZero         :: SBV a -> SBool
  --       fpIsInfinite     :: SBV a -> SBool
  --       fpIsNaN          :: SBV a -> SBool
  --       fpIsNegative     :: SBV a -> SBool
  --       fpIsPositive     :: SBV a -> SBool
  --       fpIsNegativeZero :: SBV a -> SBool
  --       fpIsPositiveZero :: SBV a -> SBool
  --       fpIsPoint        :: SBV a -> SBool

{- HLint ignore module "Reduce duplication" -}
