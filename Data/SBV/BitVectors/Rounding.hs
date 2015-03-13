-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.Rounding
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Implementation of floating-point operations that know about rounding-modes
-----------------------------------------------------------------------------

module Data.SBV.BitVectors.Rounding (RoundingFloat(..)) where

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.Model ()  -- instances only

-- | A class of floating-point (IEEE754) operations that behave
-- differently based on rounding modes. Note that we will never
-- concretely evaluate these, but rather pass down to the SMT solver
-- even when we have a concrete rounding mode supported by Haskell.
-- (i.e., round-to-nearest even.) The extra complexity is just not
-- worth it to support constant folding in that rare case; and if
-- the rounding mode is already round-to-nearest-even then end-users simply
-- use the usual Num instances. (Except for FMA obviously, which has no
-- Haskell equivalent.)
class (SymWord a, Floating a) => RoundingFloat a where
  fpAdd  :: SRoundingMode -> SBV a -> SBV a -> SBV a
  fpSub  :: SRoundingMode -> SBV a -> SBV a -> SBV a
  fpMul  :: SRoundingMode -> SBV a -> SBV a -> SBV a
  fpDiv  :: SRoundingMode -> SBV a -> SBV a -> SBV a
  fpFMA  :: SRoundingMode -> SBV a -> SBV a -> SBV a -> SBV a
  fpSqrt :: SRoundingMode -> SBV a -> SBV a

  -- Default definitions simply piggy back onto FPRound
  fpAdd  = lift2Rm "fp.add"
  fpSub  = lift2Rm "fp.sub"
  fpMul  = lift2Rm "fp.mul"
  fpDiv  = lift2Rm "fp.div"
  fpFMA  = lift3Rm "fp.fma"
  fpSqrt = lift1Rm "fp.sqrt"

-- | Lift a 1 arg floating point UOP
lift1Rm :: (SymWord a, Floating a) => String -> SRoundingMode -> SBV a -> SBV a
lift1Rm w m a = SBV k $ Right $ cache r
  where k = kindOf a
        r st = do swm <- sbvToSW st m
                  swa <- sbvToSW st a
                  newExpr st k (SBVApp (FPRound w) [swm, swa])

-- | Lift a 2 arg floating point UOP
lift2Rm :: (SymWord a, Floating a) => String -> SRoundingMode -> SBV a -> SBV a -> SBV a
lift2Rm w m a b = SBV k $ Right $ cache r
  where k = kindOf a
        r st = do swm <- sbvToSW st m
                  swa <- sbvToSW st a
                  swb <- sbvToSW st b
                  newExpr st k (SBVApp (FPRound w) [swm, swa, swb])

-- | Lift a 3 arg floating point UOP
lift3Rm :: (SymWord a, Floating a) => String -> SRoundingMode -> SBV a -> SBV a -> SBV a -> SBV a
lift3Rm w m a b c = SBV k $ Right $ cache r
  where k = kindOf a
        r st = do swm <- sbvToSW st m
                  swa <- sbvToSW st a
                  swb <- sbvToSW st b
                  swc <- sbvToSW st c
                  newExpr st k (SBVApp (FPRound w) [swm, swa, swb, swc])

-- | SFloat instance
instance RoundingFloat Float

-- | SDouble instance
instance RoundingFloat Double

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
