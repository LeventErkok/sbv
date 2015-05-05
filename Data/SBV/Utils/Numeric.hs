-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Utils.Numeric
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Various number related utilities
-----------------------------------------------------------------------------

module Data.SBV.Utils.Numeric where

-- | A variant of round; except defaulting to 0 when fed NaN or Infinity
round0 :: (RealFloat a, RealFrac a, Integral b) => a -> b
round0 x
 | isNaN x || isInfinite x = 0
 | True                    = round x

-- | A variant of toRational; except defaulting to 0 when fed NaN or Infinity
ratio0 :: (RealFloat a, RealFrac a) => a -> Rational
ratio0 x
 | isNaN x || isInfinite x = 0
 | True                    = toRational x

-- | The SMT-Lib (in particular Z3) implementation for min/max for floats does not agree with
-- Haskell's; and also it does not agree with what the hardware does. Sigh.. See:
--      <https://ghc.haskell.org/trac/ghc/ticket/10378>
--      <https://github.com/Z3Prover/z3/issues/68>
-- So, we codify here what the Z3 (SMTLib) is implementing for maxFP.
-- The discrepancy with Haskell is that the NaN propagation doesn't work in Haskell
-- The discrepancy with x86 is that given +0/-0, x86 returns the second argument; SMTLib returns +0
maxFP :: RealFloat a => a -> a -> a
maxFP x y
   | isNaN x              = y
   | isNaN y              = x
-- | (x == 0) && (y == 0) = y   -- Corresponds to x86 instructions, consider x=+0, y=-0 or vice versa
   | (x == 0) && (y == 0) = 0   -- Corresponds to SMTLib
   | x > y                = x
   | True                 = y

-- | SMTLib compliant definition for 'minFP'. See the comments for 'maxFP'.
minFP :: RealFloat a => a -> a -> a
minFP x y
   | isNaN x              = y
   | isNaN y              = x
-- | (x == y) && (y == 0) = y   -- Corresponds to x86 instructions, consider x=+0, y=-0 or vice versa
   | (x == y) && (y == 0) = 0   -- Corresponds to SMTLib
   | x < y                = x
   | True                 = y

-- | Convert double to float and back. Essentially @fromRational . toRational@
-- except careful on NaN, Infinities, and -0.
fp2fp :: (RealFloat a, RealFloat b) => a -> b
fp2fp x
 | isNaN x               =  0 / 0
 | isInfinite x && x < 0 = -1 / 0
 | isInfinite x          =  1 / 0
 | isNegativeZero x      = negate 0
 | True                  = fromRational (toRational x)

-- | Compute the "floating-point" remainder function, the float/double value that
-- remains from the division of @x@ and @y@.
fpRemH :: RealFloat a => a -> a -> a
fpRemH x y = x - y * fromInteger (round (x / y))

-- | Convert a float to the nearest integral representable in that type
fpRoundToIntegralH :: RealFloat a => a -> a
fpRoundToIntegralH x
  | isNaN x      = x
  | x == 0       = x
  | isInfinite x = x
  | True         = fromInteger (round x)

-- | Check that two floats are the exact same values, i.e., +0/-0 does not
-- compare equal, and NaN's compare equal to themselves.
fpEqualObjectH :: RealFloat a => a -> a -> Bool
fpEqualObjectH a b
  | isNaN a          = isNaN b
  | isNegativeZero a = isNegativeZero b
  | isNegativeZero b = isNegativeZero a
  | True             = a == b
