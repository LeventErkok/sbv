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
fpRound0 :: (RealFloat a, RealFrac a, Integral b) => a -> b
fpRound0 x
 | isNaN x || isInfinite x = 0
 | True                    = round x

-- | A variant of toRational; except defaulting to 0 when fed NaN or Infinity
fpRatio0 :: (RealFloat a, RealFrac a) => a -> Rational
fpRatio0 x
 | isNaN x || isInfinite x = 0
 | True                    = toRational x

-- | The SMT-Lib (in particular Z3) implementation for min/max for floats does not agree with
-- Haskell's; and also it does not agree with what the hardware does. Sigh.. See:
--      <https://ghc.haskell.org/trac/ghc/ticket/10378>
--      <https://github.com/Z3Prover/z3/issues/68>
-- So, we codify here what the Z3 (SMTLib) is implementing for fpMax.
-- The discrepancy with Haskell is that the NaN propagation doesn't work in Haskell
-- The discrepancy with x86 is that given +0/-0, x86 returns the second argument; SMTLib returns +0
fpMaxH :: RealFloat a => a -> a -> a
fpMaxH x y
   | isNaN x                              = y
   | isNaN y                              = x
   | isNegativeZero x && isNegativeZero y = -0.0
   | (x == 0) && (y == 0)                 =  0.0   -- Corresponds to SMTLib. For x86 semantics, we'd return 'y' here. (Matters when x=+0, y=-0 or vice versa)
   | x > y                                = x
   | True                                 = y

-- | SMTLib compliant definition for 'fpMin'. See the comments for 'fpMax'.
fpMinH :: RealFloat a => a -> a -> a
fpMinH x y
   | isNaN x                              = y
   | isNaN y                              = x
   | isNegativeZero x && isNegativeZero y = -0.0
   | (x == y) && (y == 0)                 =  0.0   -- Corresponds to SMTLib. For x86 semantics, we'd return 'y' here. (Matters when x=+0, y=-0 or vice versa)
   | x < y                                = x
   | True                                 = y

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
-- remains from the division of @x@ and @y@. There are strict rules around 0's, Infinities,
-- and NaN's as coded below, See <http://smt-lib.org/papers/BTRW14.pdf>, towards the
-- end of section 4.c.
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
        d | rd > 0 = floor   rd
          | True   = ceiling rd
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

-- | Check if a number is "normal." Note that +0/-0 is not considered a normal-number
-- and also this is not simply the negation of isDenormalized!
fpIsNormalizedH :: RealFloat a => a -> Bool
fpIsNormalizedH x = not (isDenormalized x || isInfinite x || isNaN x || x == 0)
