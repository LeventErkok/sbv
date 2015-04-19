-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.Floating
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Implementation of floating-point operations mapping to SMT-Lib2 floats
-----------------------------------------------------------------------------

module Data.SBV.BitVectors.Floating (IEEEFloating(..)) where

import Control.Monad (join)

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.Model ()  -- instances only

-- | A class of floating-point (IEEE754) operations, some of
-- which behave differently based on rounding modes. Note that unless
-- the rounding mode is concretely RoundNearestTiesToEven, we will
-- not concretely evaluate these, but rather pass down to the SMT solver
class (SymWord a, RealFloat a) => IEEEFloating a where
  fpAbs             ::                  SBV a -> SBV a
  fpNeg             ::                  SBV a -> SBV a
  fpAdd             :: SRoundingMode -> SBV a -> SBV a -> SBV a
  fpSub             :: SRoundingMode -> SBV a -> SBV a -> SBV a
  fpMul             :: SRoundingMode -> SBV a -> SBV a -> SBV a
  fpDiv             :: SRoundingMode -> SBV a -> SBV a -> SBV a
  fpFMA             :: SRoundingMode -> SBV a -> SBV a -> SBV a -> SBV a
  fpSqrt            :: SRoundingMode -> SBV a -> SBV a
  fpRem             ::                  SBV a -> SBV a -> SBV a
  fpRoundToIntegral :: SRoundingMode -> SBV a -> SBV a
  fpMin             ::                  SBV a -> SBV a -> SBV a
  fpMax             ::                  SBV a -> SBV a -> SBV a
  fpEqualObject     ::                  SBV a -> SBV a -> SBool

  -- Default definitions. Minimal complete definition: None! All should be taken care by defaults
  -- Note that we never evaluate FMA concretely, as there's no fma operator in Haskell
  fpAbs             = lift1  "fp.abs"             (Just abs)      Nothing
  fpNeg             = lift1  "fp.neg"             (Just negate)   Nothing
  fpAdd             = lift2  "fp.add"             (Just (+))      . Just
  fpSub             = lift2  "fp.sub"             (Just (-))      . Just
  fpMul             = lift2  "fp.mul"             (Just (*))      . Just
  fpDiv             = lift2  "fp.div"             (Just (/))      . Just
  fpFMA             = lift3  "fp.fma"             Nothing         . Just
  fpSqrt            = lift1  "fp.sqrt"            (Just sqrt)     . Just
  fpRem             = lift2  "fp.rem"             (Just fprem)    Nothing where fprem x y = x - y * fromInteger (round (x / y))
  fpRoundToIntegral = lift1  "fp.roundToIntegral" (Just fpRound)  . Just  where fpRound   = fromInteger . round
  fpMin             = lift2  "fp.min"             (Just min)      Nothing
  fpMax             = lift2  "fp.max"             (Just max)      Nothing
  fpEqualObject     = lift2B "="                  (Just fpSame)   Nothing

-- | Return true if these two floats are "the same", i.e., nan compares equal to nan, but -0 doesn't compare equal to +0
-- syntactic equality, in a sense.
fpSame :: (RealFloat a, Eq a) => a -> a -> Bool
fpSame a b
  | isNaN a          = isNaN b
  | isNegativeZero a = isNegativeZero b
  | isNegativeZero b = isNegativeZero a
  -- NB. Equality does the right thing on infinities, so no special treatment is necessary
  | True             = a == b

-- | Concretely evaluate one arg function, if rounding mode is RoundNearestTiesToEven and we have enough concrete data
concEval1 :: (SymWord a, Floating a) => Maybe (a -> a) -> Maybe SRoundingMode -> SBV a -> Maybe (SBV a)
concEval1 mbOp mbRm a = do op <- mbOp
                           v  <- unliteral a
                           case join (unliteral `fmap` mbRm) of
                             Nothing                     -> (Just . literal) (op v)
                             Just RoundNearestTiesToEven -> (Just . literal) (op v)
                             _                           -> Nothing

-- | Concretely evaluate two arg function, if rounding mode is RoundNearestTiesToEven and we have enough concrete data
concEval2 :: (SymWord a, Floating a) => Maybe (a -> a -> a) -> Maybe SRoundingMode -> SBV a -> SBV a -> Maybe (SBV a)
concEval2 mbOp mbRm a b  = do op <- mbOp
                              v1 <- unliteral a
                              v2 <- unliteral b
                              case join (unliteral `fmap` mbRm) of
                                Nothing                     -> (Just . literal) (v1 `op` v2)
                                Just RoundNearestTiesToEven -> (Just . literal) (v1 `op` v2)
                                _                           -> Nothing

-- | Concretely evaluate a bool producing two arg function, if rounding mode is RoundNearestTiesToEven and we have enough concrete data
concEval2B :: (SymWord a, Floating a) => Maybe (a -> a -> Bool) -> Maybe SRoundingMode -> SBV a -> SBV a -> Maybe SBool
concEval2B mbOp mbRm a b  = do op <- mbOp
                               v1 <- unliteral a
                               v2 <- unliteral b
                               case join (unliteral `fmap` mbRm) of
                                 Nothing                     -> (Just . literal) (v1 `op` v2)
                                 Just RoundNearestTiesToEven -> (Just . literal) (v1 `op` v2)
                                 _                           -> Nothing

-- | Concretely evaluate two arg function, if rounding mode is RoundNearestTiesToEven and we have enough concrete data
concEval3 :: (SymWord a, Floating a) => Maybe (a -> a -> a -> a) -> Maybe SRoundingMode -> SBV a -> SBV a -> SBV a -> Maybe (SBV a)
concEval3 mbOp mbRm a b c = do op <- mbOp
                               v1 <- unliteral a
                               v2 <- unliteral b
                               v3 <- unliteral c
                               case join (unliteral `fmap` mbRm) of
                                 Nothing                     -> (Just . literal) (op v1 v2 v3)
                                 Just RoundNearestTiesToEven -> (Just . literal) (op v1 v2 v3)
                                 _                           -> Nothing

-- | Add the converted rounding mode if given as an argument
addRM :: State -> Maybe SRoundingMode -> [SW] -> IO [SW]
addRM _  Nothing   as = return as
addRM st (Just rm) as = do swm <- sbvToSW st rm
                           return (swm : as)

-- | Lift a 1 arg FP-op
lift1 :: (SymWord a, Floating a) => String -> Maybe (a -> a) -> Maybe SRoundingMode -> SBV a -> SBV a
lift1 w mbOp mbRm a
  | Just cv <- concEval1 mbOp mbRm a
  = cv
  | True
  = SBV $ SVal k $ Right $ cache r
  where k    = kindOf a
        r st = do swa  <- sbvToSW st a
                  args <- addRM st mbRm [swa]
                  newExpr st k (SBVApp (IEEEFP w) args)

-- | Lift a 2 arg FP-op
lift2 :: (SymWord a, Floating a) => String -> Maybe (a -> a -> a) -> Maybe SRoundingMode -> SBV a -> SBV a -> SBV a
lift2 w mbOp mbRm a b
  | Just cv <- concEval2 mbOp mbRm a b
  = cv
  | True
  = SBV $ SVal k $ Right $ cache r
  where k    = kindOf a
        r st = do swa  <- sbvToSW st a
                  swb  <- sbvToSW st b
                  args <- addRM st mbRm [swa, swb]
                  newExpr st k (SBVApp (IEEEFP w) args)

-- | Lift a 2 arg FP-op, producing bool
lift2B :: (SymWord a, Floating a) => String -> Maybe (a -> a -> Bool) -> Maybe SRoundingMode -> SBV a -> SBV a -> SBool
lift2B w mbOp mbRm a b
  | Just cv <- concEval2B mbOp mbRm a b
  = cv
  | True
  = SBV $ SVal KBool $ Right $ cache r
  where r st = do swa  <- sbvToSW st a
                  swb  <- sbvToSW st b
                  args <- addRM st mbRm [swa, swb]
                  newExpr st KBool (SBVApp (IEEEFP w) args)

-- | Lift a 3 arg FP-op
lift3 :: (SymWord a, Floating a) => String -> Maybe (a -> a -> a -> a) -> Maybe SRoundingMode -> SBV a -> SBV a -> SBV a -> SBV a
lift3 w mbOp mbRm a b c
  | Just cv <- concEval3 mbOp mbRm a b c
  = cv
  | True
  = SBV $ SVal k $ Right $ cache r
  where k    = kindOf a
        r st = do swa  <- sbvToSW st a
                  swb  <- sbvToSW st b
                  swc  <- sbvToSW st c
                  args <- addRM st mbRm [swa, swb, swc]
                  newExpr st k (SBVApp (IEEEFP w) args)

-- | SFloat instance
instance IEEEFloating Float

-- | SDouble instance
instance IEEEFloating Double

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
