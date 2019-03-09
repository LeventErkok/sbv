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
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.SBV.Core.Floating (
         IEEEFloating(..), IEEEFloatConvertible(..)
       , sFloatAsSWord32, sDoubleAsSWord64, sWord32AsSFloat, sWord64AsSDouble
       , blastSFloat, blastSDouble
       , sFloatAsComparableSWord32, sDoubleAsComparableSWord64
       ) where

import qualified Data.Numbers.CrackNum as CN (wordToFloat, wordToDouble, floatToWord, doubleToWord)

import Data.Int            (Int8,  Int16,  Int32,  Int64)
import Data.Word           (Word8, Word16, Word32, Word64)

import Data.Proxy

import Data.SBV.Core.AlgReals (isExactRational)

import Data.SBV.Core.Data
import Data.SBV.Core.Model
import Data.SBV.Core.Symbolic (addSValOptGoal)

import Data.SBV.Utils.Numeric

-- For doctest use only
--
-- $setup
-- >>> :set -XTypeApplications
-- >>> :set -XRankNTypes
-- >>> :set -XScopedTypeVariables
-- >>> import Data.SBV.Provers.Prover (prove)

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

-- | Capture convertability from/to FloatingPoint representations.
--
-- Conversions to float: 'toSFloat' and 'toSDouble' simply return the
-- nearest representable float from the given type based on the rounding
-- mode provided.
--
-- Conversions from float: 'fromSFloat' and 'fromSDouble' functions do
-- the reverse conversion. However some care is needed when given values
-- that are not representable in the integral target domain. For instance,
-- converting an 'SFloat' to an 'SInt8' is problematic. The rules are as follows:
--
-- If the input value is a finite point and when rounded in the given rounding mode to an
-- integral value lies within the target bounds, then that result is returned.
-- (This is the regular interpretation of rounding in IEEE754.)
--
-- Otherwise (i.e., if the integral value in the float or double domain) doesn't
-- fit into the target type, then the result is unspecified. Note that if the input
-- is @+oo@, @-oo@, or @NaN@, then the result is unspecified.
--
-- Due to the unspecified nature of conversions, SBV will never constant fold
-- conversions from floats to integral values. That is, you will always get a
-- symbolic value as output. (Conversions from floats to other floats will be
-- constant folded. Conversions from integral values to floats will also be
-- constant folded.)
--
-- Note that unspecified really means unspecified: In particular, SBV makes
-- no guarantees about matching the behavior between what you might get in
-- Haskell, via SMT-Lib, or the C-translation. If the input value is out-of-bounds
-- as defined above, or is @NaN@ or @oo@ or @-oo@, then all bets are off. In particular
-- C and SMTLib are decidedly undefine this case, though that doesn't mean they do the
-- same thing! Same goes for Haskell, which seems to convert via Int64, but we do
-- not model that behavior in SBV as it doesn't seem to be intentional nor well documented.
--
-- You can check for @NaN@, @oo@ and @-oo@, using the predicates 'fpIsNaN', 'fpIsInfinite',
-- and 'fpIsPositive', 'fpIsNegative' predicates, respectively; and do the proper conversion
-- based on your needs. (0 is a good choice, as are min/max bounds of the target type.)
--
-- Currently, SBV provides no predicates to check if a value would lie within range for a
-- particular conversion task, as this depends on the rounding mode and the types involved
-- and can be rather tricky to determine. (See <http://github.com/LeventErkok/sbv/issues/456>
-- for a discussion of the issues involved.) In a future release, we hope to be able to
-- provide underflow and overflow predicates for these conversions as well.
class SymVal a => IEEEFloatConvertible a where
  -- | Convert from an IEEE74 single precision float.
  fromSFloat :: SRoundingMode -> SFloat -> SBV a
  fromSFloat = genericFromFloat

  -- | Convert to an IEEE-754 Single-precision float.
  --
  -- >>> :{
  -- roundTrip :: forall a. (Eq a, IEEEFloatConvertible a) => SRoundingMode -> SBV a -> SBool
  -- roundTrip m x = fromSFloat m (toSFloat m x) .== x
  -- :}
  --
  -- >>> prove $ roundTrip @Int8
  -- Q.E.D.
  -- >>> prove $ roundTrip @Word8
  -- Q.E.D.
  -- >>> prove $ roundTrip @Int16
  -- Q.E.D.
  -- >>> prove $ roundTrip @Word16
  -- Q.E.D.
  -- >>> prove $ roundTrip @Int32
  -- Falsifiable. Counter-example:
  --   s0 = RoundNearestTiesToEven :: RoundingMode
  --   s1 =            -2130176960 :: Int32
  --
  -- Note how we get a failure on `Int32`. The counter-example value is not representable exactly as a single precision float:
  --
  -- >>> toRational (-2130176960 :: Float)
  -- (-2130177024) % 1
  --
  -- Note how the numerator is different, it is off by 64. This is hardly surprising, since floats become sparser as
  -- the magnitude increases to be able to cover all the integer values representable.
  toSFloat :: SRoundingMode -> SBV a -> SFloat

  -- default definition if we have an integral like
  default toSFloat :: Integral a => SRoundingMode -> SBV a -> SFloat
  toSFloat = genericToFloat (Just . fromRational . fromIntegral)

  -- | Convert from an IEEE74 double precision float.
  fromSDouble :: SRoundingMode -> SDouble -> SBV a
  fromSDouble = genericFromFloat

  -- | Convert to an IEEE-754 Double-precision float.
  --
  -- >>> :{
  -- roundTrip :: forall a. (Eq a, IEEEFloatConvertible a) => SRoundingMode -> SBV a -> SBool
  -- roundTrip m x = fromSDouble m (toSDouble m x) .== x
  -- :}
  --
  -- >>> prove $ roundTrip @Int8
  -- Q.E.D.
  -- >>> prove $ roundTrip @Word8
  -- Q.E.D.
  -- >>> prove $ roundTrip @Int16
  -- Q.E.D.
  -- >>> prove $ roundTrip @Word16
  -- Q.E.D.
  -- >>> prove $ roundTrip @Int32
  -- Q.E.D.
  -- >>> prove $ roundTrip @Word32
  -- Q.E.D.
  -- >>> prove $ roundTrip @Int64
  -- Falsifiable. Counter-example:
  --   s0 = RoundNearestTiesToEven :: RoundingMode
  --   s1 =    4611686018427387902 :: Int64
  --
  -- Just like in the `SFloat` case, once we reach 64-bits, we no longer can exactly represent the
  -- integer value for all possible values:
  --
  -- >>> toRational (4611686018427387902 ::Double)
  -- 4611686018427387904 % 1
  --
  -- In this case the numerator is off by 2!
  toSDouble :: SRoundingMode -> SBV a -> SDouble

  -- default definition if we have an integral like
  default toSDouble :: Integral a => SRoundingMode -> SBV a -> SDouble
  toSDouble = genericToFloat (Just . fromRational . fromIntegral)

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

-- | A generic to-float converter, which will constant-fold as necessary, but only in the sRNE mode.
genericToFloat :: forall a r. (IEEEFloatConvertible a, IEEEFloating r)
               => (a -> Maybe r)     -- How to convert concretely, if possible
               -> SRoundingMode      -- Rounding mode
               -> SBV a              -- Input convertible
               -> SBV r
genericToFloat converter rm i
  | Just w <- unliteral i, Just RoundNearestTiesToEven <- unliteral rm, Just result <- converter w
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
  toSDouble     = genericToFloat (Just . fp2fp)

  fromSFloat  _  f = f
  fromSDouble rm f
    | Just RoundNearestTiesToEven <- unliteral rm
    , Just fv                     <- unliteral f
    = literal (fp2fp fv)
    | True
    = genericFromFloat rm f

instance IEEEFloatConvertible Double where
  toSFloat      = genericToFloat (Just . fp2fp)
  toSDouble _ d = d

  fromSDouble _  d = d
  fromSFloat  rm d
    | Just RoundNearestTiesToEven <- unliteral rm
    , Just dv                     <- unliteral d
    = literal (fp2fp dv)
    | True
    = genericFromFloat rm d

-- For AlgReal; be careful to only process exact rationals concretely
instance IEEEFloatConvertible AlgReal where
  toSFloat  = genericToFloat (\r -> if isExactRational r then Just (fromRational (toRational r)) else Nothing)
  toSDouble = genericToFloat (\r -> if isExactRational r then Just (fromRational (toRational r)) else Nothing)

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
concEval2 mbOp mbRm a b  = do op <- mbOp
                              v1 <- unliteral a
                              v2 <- unliteral b
                              case unliteral =<< mbRm of
                                Nothing                     -> (Just . literal) (v1 `op` v2)
                                Just RoundNearestTiesToEven -> (Just . literal) (v1 `op` v2)
                                _                           -> Nothing

-- | Concretely evaluate a bool producing two arg function, if rounding mode is RoundNearestTiesToEven and we have enough concrete data
concEval2B :: SymVal a => Maybe (a -> a -> Bool) -> Maybe SRoundingMode -> SBV a -> SBV a -> Maybe SBool
concEval2B mbOp mbRm a b  = do op <- mbOp
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
sFloatAsSWord32 fVal
  | Just f <- unliteral fVal, not (isNaN f)
  = literal (CN.floatToWord f)
  | True
  = SBV (SVal w32 (Right (cache y)))
  where w32  = KBounded False 32
        y st = do cg <- isCodeGenMode st
                  if cg
                     then do f <- sbvToSV st fVal
                             newExpr st w32 (SBVApp (IEEEFP (FP_Reinterpret KFloat w32)) [f])
                     else do n   <- internalVariable st w32
                             ysw <- newExpr st KFloat (SBVApp (IEEEFP (FP_Reinterpret w32 KFloat)) [n])
                             internalConstraint st False [] $ unSBV $ fVal `fpIsEqualObject` SBV (SVal KFloat (Right (cache (\_ -> return ysw))))
                             return n

-- | Convert an 'SDouble' to an 'SWord64', preserving the bit-correspondence. Note that since the
-- representation for @NaN@s are not unique, this function will return a symbolic value when given a
-- concrete @NaN@.
--
-- See the implementation note for 'sFloatAsSWord32', as it applies here as well.
sDoubleAsSWord64 :: SDouble -> SWord64
sDoubleAsSWord64 fVal
  | Just f <- unliteral fVal, not (isNaN f)
  = literal (CN.doubleToWord f)
  | True
  = SBV (SVal w64 (Right (cache y)))
  where w64  = KBounded False 64
        y st = do cg <- isCodeGenMode st
                  if cg
                     then do f <- sbvToSV st fVal
                             newExpr st w64 (SBVApp (IEEEFP (FP_Reinterpret KDouble w64)) [f])
                     else do n   <- internalVariable st w64
                             ysw <- newExpr st KDouble (SBVApp (IEEEFP (FP_Reinterpret w64 KDouble)) [n])
                             internalConstraint st False [] $ unSBV $ fVal `fpIsEqualObject` SBV (SVal KDouble (Right (cache (\_ -> return ysw))))
                             return n

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

-- | Reinterpret the bits in a 32-bit word as a single-precision floating point number
sWord32AsSFloat :: SWord32 -> SFloat
sWord32AsSFloat fVal
  | Just f <- unliteral fVal = literal $ CN.wordToFloat f
  | True                     = SBV (SVal KFloat (Right (cache y)))
  where y st = do xsv <- sbvToSV st fVal
                  newExpr st KFloat (SBVApp (IEEEFP (FP_Reinterpret (kindOf fVal) KFloat)) [xsv])

-- | Reinterpret the bits in a 32-bit word as a single-precision floating point number
sWord64AsSDouble :: SWord64 -> SDouble
sWord64AsSDouble dVal
  | Just d <- unliteral dVal = literal $ CN.wordToDouble d
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

-- | Convert a double to a comparable 'SWord64'. The trick is to ignore the
-- sign of -0, and if it's a negative value flip all the bits, and otherwise
-- only flip the sign bit. This is known as the lexicographic ordering on doubles
-- and it works as long as you do not have a @NaN@.
sDoubleAsComparableSWord64 :: SDouble -> SWord64
sDoubleAsComparableSWord64 d = ite (fpIsNegativeZero d) (sDoubleAsComparableSWord64 0) (fromBitsBE $ sNot sb : ite sb (map sNot rest) rest)
  where (sb : rest) = blastBE $ sDoubleAsSWord64 d

-- | 'Float' instance for 'Metric' goes through the lexicographic ordering on 'Word32'.
-- It implicitly makes sure that the value is not @NaN@.
instance Metric Float where

   type MetricSpace Float = Word32
   toMetricSpace          = sFloatAsComparableSWord32
   fromMetricSpace        = sWord32AsSFloat

   msMinimize nm o = do constrain $ sNot $ fpIsNaN o
                        addSValOptGoal $ unSBV `fmap` Minimize nm (toMetricSpace o)

   msMaximize nm o = do constrain $ sNot $ fpIsNaN o
                        addSValOptGoal $ unSBV `fmap` Maximize nm (toMetricSpace o)

-- | 'Double' instance for 'Metric' goes through the lexicographic ordering on 'Word64'.
-- It implicitly makes sure that the value is not @NaN@.
instance Metric Double where

   type MetricSpace Double = Word64
   toMetricSpace           = sDoubleAsComparableSWord64
   fromMetricSpace         = sWord64AsSDouble

   msMinimize nm o = do constrain $ sNot $ fpIsNaN o
                        addSValOptGoal $ unSBV `fmap` Minimize nm (toMetricSpace o)

   msMaximize nm o = do constrain $ sNot $ fpIsNaN o
                        addSValOptGoal $ unSBV `fmap` Maximize nm (toMetricSpace o)

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
