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

{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Data.SBV.Core.Floating (
         IEEEFloating(..), IEEEFloatConvertible(..)
       , sFloatAsSWord32, sDoubleAsSWord64, sWord32AsSFloat, sWord64AsSDouble
       , blastSFloat, blastSDouble
       ) where

import qualified Data.Numbers.CrackNum as CN (wordToFloat, wordToDouble, floatToWord, doubleToWord)

import Data.Int            (Int8,  Int16,  Int32,  Int64)
import Data.Word           (Word8, Word16, Word32, Word64)

import Data.Proxy

import Data.SBV.Core.Data
import Data.SBV.Core.Model
import Data.SBV.Core.AlgReals (isExactRational)

import Data.SBV.Utils.Numeric

import Data.SBV.Utils.FloatConversionBounds

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
-- Special values: 'fromSFloat' and 'fromSDouble' functions need
-- some care when given values that are not representable in the
-- integral target domain. For instance, converting an 'SFloat' to
-- an 'SInt8'. The rules are as follows:
--
-- If the input is @NaN@, @+oo@ or @-oo@], conversion produces 0.
--
-- If the input value is out-of-range for the target type (happens when
-- the target is a signed or unsigned bitvector), then the semantics
-- is as if we first convert the input to an 'Int64' or 'Word64'
-- depending on the signedness of the target, and then convert that value
-- to the target type. Note that this is seemingly the behavior of Haskell
-- (though documentation is hard to come by in this regard!), but not
-- necessarily C, where out-of-bounds conversions are explicitly stated
-- to be undefined. We follow what we observed Haskell to be doing here
-- in our experiments.
--
-- If you want precise control, you can use the following predicates:
-- To detect @NaN@, use 'fpIsNaN'. To detect infinity, use 'fpIsInfinite'
-- together with 'fpIsPositive' and 'fpIsNegative' to determine the sign
-- of the infinity if necessary. When you have a regular value (i.e.,
-- something that satisfies 'fpIsPoint'), then you can use 'sFloatInRange'
-- and 'sDoubleInRange' to determine if it is within the allowed conversion
-- range.
class HasKind a => IEEEFloatConvertible a where
  -- | Convert from an IEEE74 single precision float.
  fromSFloat :: SRoundingMode -> SFloat -> SBV a

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
  --   s1 =             -268435454 :: Int32
  --
  -- Note how we get a failure on `Int32`. The value @-268435454@ is not representable exactly
  -- as a single precision float:
  --
  -- >>> toRational (-268435454 :: Float)
  -- (-268435456) % 1
  --
  -- Note how the numerator is different!
  toSFloat    :: SRoundingMode -> SBV a -> SFloat

  -- | Convert from an IEEE74 double precision float.
  fromSDouble :: SRoundingMode -> SDouble -> SBV a

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
  --   s1 =   -1152919305583591360 :: Int64
  --
  -- Just like in the `SFloat` case, once we reach 64-bits, we no longer can exactly represent the
  -- integer value for all possible values:
  --
  -- >>> toRational (-1152919305583591360 :: Double)
  -- (-1152919305583591424) % 1
  --
  -- Again the numerator is different!
  toSDouble :: SRoundingMode -> SBV a -> SDouble

  -- | Is the given float in range for the conversion?
  sFloatInRange :: SRoundingMode -> Proxy a -> SFloat -> SBool

  -- | Range of doubles that can be safely mapped to this type, per rounding mode
  sDoubleInRange :: SRoundingMode -> Proxy a -> SDouble -> SBool

  {-# MINIMAL fromSDouble, toSDouble, fromSFloat, toSFloat #-}

  sFloatInRange rm pa f = sAnd [check m fr | ((k, m), (fr, _)) <- conversionBounds, k == kindOf pa]
    where check m (lb, ub) = literal m .== rm .=> (f .>= literal lb .&& f .<= literal ub)

  sDoubleInRange rm pa d = sAnd [check m dr | ((k, m), (_, dr)) <- conversionBounds, k == kindOf pa]
    where check m (lb, ub) = literal m .== rm .=> (d .>= literal lb .&& d .<= literal ub)

-- | A generic converter that will work for most of our instances. (But not all!)
genericFPConverter :: forall a r. (SymVal a, HasKind r, SymVal r, Num r)
                   => Maybe (a -> Bool)        -- Is the concrete value OK to convert?
                   -> Maybe (SBV a -> SBool)   -- Is the symbolic value OK to convert?
                   -> Maybe (SBV a -> SBool)   -- Is the value within range. (NB. We perform this check in both above cases.)
                   -> (a -> r)                 -- How to convert concretely
                   -> SRoundingMode            -- Rounding mode
                   -> SBV a                    -- Input float/double
                   -> SBV r
genericFPConverter mbConcreteOK mbSymbolicOK mbInRangeOK converter rm f
  | Just w <- unliteral f, Just RoundNearestTiesToEven <- unliteral rm, maybe True ($ w) mbConcreteOK
  = literal $ converter w

  | Just symCheck <- mbSymbolicOK
  = ite (symCheck f) result (literal 0)

  | True
  = result

  where kFrom   = kindOf f
        kTo     = kindOf (Proxy @r)

        -- If we're in bounds, simply do the conversion:
        resultViaDirect = SBV (SVal kTo (Right (cache y)))
          where y st = do msv <- sbvToSV st rm
                          xsv <- sbvToSV st f
                          newExpr st kTo (SBVApp (IEEEFP (FP_Cast kFrom kTo msv)) [xsv])

        -- If we're out-of-bounds, convert to Int64/Word64 depending on the signedness, and then cast away:
        resultViaIntermediate = SBV (SVal kTo (Right (cache y)))
          where kIntermediate = KBounded (hasSign kTo) 64
                y st = do msv  <- sbvToSV st rm
                          xsv  <- sbvToSV st f
                          ires <- newExpr st kIntermediate (SBVApp (IEEEFP (FP_Cast kFrom         kIntermediate msv)) [xsv])
                          newExpr         st kTo           (SBVApp (KindCast        kIntermediate kTo              )  [ires])

        result = case mbInRangeOK of
                   Nothing -> resultViaDirect
                   Just c  -> ite (c f) resultViaDirect resultViaIntermediate

-- | Check that a given float is a point
ptCheck :: IEEEFloating a => Maybe (SBV a -> SBool)
ptCheck = Just fpIsPoint

instance IEEEFloatConvertible Int8 where
  fromSFloat  rm = genericFPConverter Nothing ptCheck (Just (sFloatInRange  rm (Proxy @Int8))) (fromIntegral . (fpRound0 :: Float  -> Integer)) rm
  toSFloat       = genericFPConverter Nothing Nothing Nothing                                  (fromRational . fromIntegral)
  fromSDouble rm = genericFPConverter Nothing ptCheck (Just (sDoubleInRange rm (Proxy @Int8))) (fromIntegral . (fpRound0 :: Double -> Integer)) rm
  toSDouble      = genericFPConverter Nothing Nothing Nothing                                  (fromRational . fromIntegral)

instance IEEEFloatConvertible Int16 where
  fromSFloat  rm = genericFPConverter Nothing ptCheck (Just (sFloatInRange  rm (Proxy @Int16))) (fromIntegral . (fpRound0 :: Float  -> Integer)) rm
  toSFloat       = genericFPConverter Nothing Nothing Nothing                                   (fromRational . fromIntegral)
  fromSDouble rm = genericFPConverter Nothing ptCheck (Just (sDoubleInRange rm (Proxy @Int16))) (fromIntegral . (fpRound0 :: Double -> Integer)) rm
  toSDouble      = genericFPConverter Nothing Nothing Nothing                                   (fromRational . fromIntegral)

instance IEEEFloatConvertible Int32 where
  fromSFloat  rm = genericFPConverter Nothing ptCheck (Just (sFloatInRange  rm (Proxy @Int32))) (fromIntegral . (fpRound0 :: Float  -> Integer)) rm
  toSFloat       = genericFPConverter Nothing Nothing Nothing                                   (fromRational . fromIntegral)
  fromSDouble rm = genericFPConverter Nothing ptCheck (Just (sDoubleInRange rm (Proxy @Int32))) (fromIntegral . (fpRound0 :: Double -> Integer)) rm
  toSDouble      = genericFPConverter Nothing Nothing Nothing                                   (fromRational . fromIntegral)

instance IEEEFloatConvertible Int64 where
  fromSFloat  rm = genericFPConverter Nothing ptCheck (Just (sFloatInRange  rm (Proxy @Int64))) (fromIntegral . (fpRound0 :: Float  -> Integer)) rm
  toSFloat       = genericFPConverter Nothing Nothing Nothing                                   (fromRational . fromIntegral)
  fromSDouble rm = genericFPConverter Nothing ptCheck (Just (sDoubleInRange rm (Proxy @Int64))) (fromIntegral . (fpRound0 :: Double -> Integer)) rm
  toSDouble      = genericFPConverter Nothing Nothing Nothing                                   (fromRational . fromIntegral)

instance IEEEFloatConvertible Word8 where
  fromSFloat  rm = genericFPConverter Nothing ptCheck (Just (sFloatInRange  rm (Proxy @Word8))) (fromIntegral . (fpRound0 :: Float  -> Integer)) rm
  toSFloat       = genericFPConverter Nothing Nothing Nothing                                   (fromRational . fromIntegral)
  fromSDouble rm = genericFPConverter Nothing ptCheck (Just (sDoubleInRange rm (Proxy @Word8))) (fromIntegral . (fpRound0 :: Double -> Integer)) rm
  toSDouble      = genericFPConverter Nothing Nothing Nothing                                   (fromRational . fromIntegral)

instance IEEEFloatConvertible Word16 where
  fromSFloat  rm = genericFPConverter Nothing ptCheck (Just (sFloatInRange  rm (Proxy @Word16))) (fromIntegral . (fpRound0 :: Float  -> Integer)) rm
  toSFloat       = genericFPConverter Nothing Nothing Nothing                                    (fromRational . fromIntegral)
  fromSDouble rm = genericFPConverter Nothing ptCheck (Just (sDoubleInRange rm (Proxy @Word16))) (fromIntegral . (fpRound0 :: Double -> Integer)) rm
  toSDouble      = genericFPConverter Nothing Nothing Nothing                                    (fromRational . fromIntegral)

instance IEEEFloatConvertible Word32 where
  fromSFloat  rm = genericFPConverter Nothing ptCheck (Just (sFloatInRange  rm (Proxy @Word32))) (fromIntegral . (fpRound0 :: Float  -> Integer)) rm
  toSFloat       = genericFPConverter Nothing Nothing Nothing                                    (fromRational . fromIntegral)
  fromSDouble rm = genericFPConverter Nothing ptCheck (Just (sDoubleInRange rm (Proxy @Word32))) (fromIntegral . (fpRound0 :: Double -> Integer)) rm
  toSDouble      = genericFPConverter Nothing Nothing Nothing                                    (fromRational . fromIntegral)

instance IEEEFloatConvertible Word64 where
  fromSFloat  rm = genericFPConverter Nothing ptCheck (Just (sFloatInRange  rm (Proxy @Word64))) (fromIntegral . (fpRound0 :: Float  -> Integer)) rm
  toSFloat       = genericFPConverter Nothing Nothing Nothing                                    (fromRational . fromIntegral)
  fromSDouble rm = genericFPConverter Nothing ptCheck (Just (sDoubleInRange rm (Proxy @Word64))) (fromIntegral . (fpRound0 :: Double -> Integer)) rm
  toSDouble      = genericFPConverter Nothing Nothing Nothing                                    (fromRational . fromIntegral)

instance IEEEFloatConvertible Float where
  fromSFloat _ f = f
  toSFloat   _ f = f
  fromSDouble    = genericFPConverter Nothing Nothing Nothing fp2fp
  toSDouble      = genericFPConverter Nothing Nothing Nothing fp2fp

instance IEEEFloatConvertible Double where
  fromSFloat      = genericFPConverter Nothing Nothing Nothing fp2fp
  toSFloat        = genericFPConverter Nothing Nothing Nothing fp2fp
  fromSDouble _ d = d
  toSDouble   _ d = d

instance IEEEFloatConvertible Integer where
  fromSFloat  = genericFPConverter Nothing ptCheck Nothing (fromIntegral . (fpRound0 :: Float -> Integer))
  toSFloat    = genericFPConverter Nothing Nothing Nothing (fromRational . fromIntegral)
  fromSDouble = genericFPConverter Nothing ptCheck Nothing (fromIntegral . (fpRound0 :: Double -> Integer))
  toSDouble   = genericFPConverter Nothing Nothing Nothing (fromRational . fromIntegral)

-- For AlgReal; be careful to only process exact rationals concretely
instance IEEEFloatConvertible AlgReal where
  fromSFloat  = genericFPConverter Nothing                ptCheck Nothing (fromRational . fpRatio0)
  toSFloat    = genericFPConverter (Just isExactRational) Nothing Nothing (fromRational . toRational)
  fromSDouble = genericFPConverter Nothing                ptCheck Nothing (fromRational . fpRatio0)
  toSDouble   = genericFPConverter (Just isExactRational) Nothing Nothing (fromRational . toRational)

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

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
