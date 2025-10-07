-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Utils.Numeric
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Various number related utilities
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Utils.Numeric (
           fpMaxH, fpMinH, fp2fp, fpRemH, fpRoundToIntegralH, fpIsEqualObjectH, fpCompareObjectH, fpIsNormalizedH
         , floatToWord, wordToFloat, doubleToWord, wordToDouble
         , RoundingMode(..), smtRoundingMode
         ) where

import Data.Word
import Data.Array.ST     (newArray, readArray, MArray, STUArray)
import Data.Array.Unsafe (castSTUArray)
import GHC.ST            (runST, ST)

import Test.QuickCheck  (Arbitrary(..), elements)

-- | The SMT-Lib (in particular Z3) implementation for min/max for floats does not agree with
-- Haskell's; and also it does not agree with what the hardware does. Sigh.. See:
--      <https://gitlab.haskell.org/ghc/ghc/-/issues/10378>
--      <http://github.com/Z3Prover/z3/issues/68>
-- So, we codify here what the Z3 (SMTLib) is implementing for fpMax.
-- The discrepancy with Haskell is that the NaN propagation doesn't work in Haskell
-- The discrepancy with x86 is that given +0/-0, x86 returns the second argument; SMTLib is non-deterministic
fpMaxH :: RealFloat a => a -> a -> a
fpMaxH x y
   | isNaN x                                  = y
   | isNaN y                                  = x
   | (isN0 x && isP0 y) || (isN0 y && isP0 x) = error "fpMaxH: Called with alternating-sign 0's. Not supported"
   | x > y                                    = x
   | True                                     = y
   where isN0   = isNegativeZero
         isP0 a = a == 0 && not (isN0 a)

-- | SMTLib compliant definition for 'Data.SBV.fpMin'. See the comments for 'Data.SBV.fpMax'.
fpMinH :: RealFloat a => a -> a -> a
fpMinH x y
   | isNaN x                                  = y
   | isNaN y                                  = x
   | (isN0 x && isP0 y) || (isN0 y && isP0 x) = error "fpMinH: Called with alternating-sign 0's. Not supported"
   | x < y                                    = x
   | True                                     = y
   where isN0   = isNegativeZero
         isP0 a = a == 0 && not (isN0 a)

-- | Convert double to float and back. Essentially @fromRational . toRational@
-- except careful on NaN, Infinities, and -0.
fp2fp :: (RealFloat a, RealFloat b) => a -> b
fp2fp x
 | isNaN x               =   0 / 0
 | isInfinite x && x < 0 = -(1 / 0)
 | isInfinite x          =   1 / 0
 | isNegativeZero x      = negate 0
 | True                  = fromRational (toRational x)

-- | Compute the "floating-point" remainder function, the float/double value that
-- remains from the division of @x@ and @y@. There are strict rules around 0's, Infinities,
-- and NaN's as coded below.
fpRemH :: RealFloat a => a -> a -> a
fpRemH x y
  | isInfinite x || isNaN x = 0 / 0
  | y == 0       || isNaN y = 0 / 0
  | isInfinite y            = x
  | True                    = pSign (x - fromRational (fromInteger d * ry))
  where rx, ry, rd :: Rational
        rx = toRational x
        ry = toRational y
        rd = rx / ry
        d :: Integer
        d = round rd
        -- If the result is 0, make sure we preserve the sign of x
        pSign r
          | r == 0 = if x < 0 || isNegativeZero x then -0.0 else 0.0
          | True   = r

-- | Convert a float to the nearest integral representable in that type
fpRoundToIntegralH :: RealFloat a => a -> a
fpRoundToIntegralH x
  | isNaN x      = x
  | x == 0       = x
  | isInfinite x = x
  | i == 0       = if x < 0 || isNegativeZero x then -0.0 else 0.0
  | True         = fromInteger i
  where i :: Integer
        i = round x

-- | Check that two floats are the exact same values, i.e., +0/-0 does not
-- compare equal, and NaN's compare equal to themselves.
fpIsEqualObjectH :: RealFloat a => a -> a -> Bool
fpIsEqualObjectH a b
  | isNaN a          = isNaN b
  | isNegativeZero a = isNegativeZero b
  | isNegativeZero b = isNegativeZero a
  | True             = a == b

-- | Ordering for floats, avoiding the +0/-0/NaN issues. Note that this is
-- essentially used for indexing into a map, so we need to be total. Thus,
-- the order we pick is:
--    NaN -oo -0 +0 +oo
-- The placement of NaN here is questionable, but immaterial.
fpCompareObjectH :: RealFloat a => a -> a -> Ordering
fpCompareObjectH a b
  | a `fpIsEqualObjectH` b   = EQ
  | isNaN a                  = LT
  | isNaN b                  = GT
  | isNegativeZero a, b == 0 = LT
  | isNegativeZero b, a == 0 = GT
  | True                     = a `compare` b

-- | Check if a number is "normal." Note that +0/-0 is not considered a normal-number
-- and also this is not simply the negation of isDenormalized!
fpIsNormalizedH :: RealFloat a => a -> Bool
fpIsNormalizedH x = not (isDenormalized x || isInfinite x || isNaN x || x == 0)

-------------------------------------------------------------------------
-- Reinterpreting float/double as word32/64 and back. Here, we use the
-- definitions from the reinterpret-cast package:
--
--     http://hackage.haskell.org/package/reinterpret-cast
--
-- The reason we steal these definitions is to make sure we keep minimal
-- dependencies and no FFI requirements anywhere.
-------------------------------------------------------------------------
-- | Reinterpret-casts a `Float` to a `Word32`.
floatToWord :: Float -> Word32
floatToWord x = runST (cast x)
{-# INLINEABLE floatToWord #-}

-- | Reinterpret-casts a `Word32` to a `Float`.
wordToFloat :: Word32 -> Float
wordToFloat x = runST (cast x)
{-# INLINEABLE wordToFloat #-}

-- | Reinterpret-casts a `Double` to a `Word64`.
doubleToWord :: Double -> Word64
doubleToWord x = runST (cast x)
{-# INLINEABLE doubleToWord #-}

-- | Reinterpret-casts a `Word64` to a `Double`.
wordToDouble :: Word64 -> Double
wordToDouble x = runST (cast x)
{-# INLINEABLE wordToDouble #-}

{-# INLINE cast #-}
cast :: (MArray (STUArray s) a (ST s), MArray (STUArray s) b (ST s)) => a -> ST s b
cast x = newArray (0 :: Int, 0) x >>= castSTUArray >>= flip readArray 0

-- | Rounding mode to be used for the IEEE floating-point operations.
-- Note that Haskell's default is 'RoundNearestTiesToEven'. If you use
-- a different rounding mode, then the counter-examples you get may not
-- match what you observe in Haskell.
data RoundingMode = RoundNearestTiesToEven  -- ^ Round to nearest representable floating point value.
                                            -- If precisely at half-way, pick the even number.
                                            -- (In this context, /even/ means the lowest-order bit is zero.)
                  | RoundNearestTiesToAway  -- ^ Round to nearest representable floating point value.
                                            -- If precisely at half-way, pick the number further away from 0.
                                            -- (That is, for positive values, pick the greater; for negative values, pick the smaller.)
                  | RoundTowardPositive     -- ^ Round towards positive infinity. (Also known as rounding-up or ceiling.)
                  | RoundTowardNegative     -- ^ Round towards negative infinity. (Also known as rounding-down or floor.)
                  | RoundTowardZero         -- ^ Round towards zero. (Also known as truncation.)
                  deriving (Show, Enum, Bounded)

-- | Arbitrary instance for 'RoundingMode'
instance Arbitrary RoundingMode where
  arbitrary = elements [minBound .. maxBound]

-- | Convert a rounding mode to the format SMT-Lib2 understands.
smtRoundingMode :: RoundingMode -> String
smtRoundingMode RoundNearestTiesToEven = "roundNearestTiesToEven"
smtRoundingMode RoundNearestTiesToAway = "roundNearestTiesToAway"
smtRoundingMode RoundTowardPositive    = "roundTowardPositive"
smtRoundingMode RoundTowardNegative    = "roundTowardNegative"
smtRoundingMode RoundTowardZero        = "roundTowardZero"
