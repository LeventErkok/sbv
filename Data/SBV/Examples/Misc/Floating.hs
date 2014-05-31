-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Misc.Floating
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Several examples involving IEEE-754 floating point numbers, i.e., single
-- precision 'Float' ('SFloat') and double precision 'Double' ('SDouble') types.
--
-- Note that arithmetic with floating point is full of surprises; due to precision
-- issues associativity of arithmetic operations typically do not hold. Also,
-- the presence of @NaN@ is always something to look out for.
-----------------------------------------------------------------------------

module Data.SBV.Examples.Misc.Floating where

import Data.SBV

-----------------------------------------------------------------------------
-- * FP addition is not associative
-----------------------------------------------------------------------------

-- | Prove that floating point addition is not associative. We have:
--
-- >>> prove assocPlus
-- Falsifiable. Counter-example:
--   s0 = -Infinity :: SFloat
--   s1 = Infinity :: SFloat
--   s2 = -9.403955e-38 :: SFloat
--
-- Indeed:
--
-- >>> let i = 1/0 :: Float
-- >>> ((-i) + i) + (-9.403955e-38) :: Float
-- NaN
-- >>> (-i) + (i + (-9.403955e-38)) :: Float
-- NaN
--
-- But keep in mind that @NaN@ does not equal itself in the floating point world! We have:
--
-- >>> let nan = 0/0 :: Float in nan == nan
-- False
assocPlus :: SFloat -> SFloat -> SFloat -> SBool
assocPlus x y z = x + (y + z) .== (x + y) + z

-- | Prove that addition is not associative, even if we ignore @NaN@/@Infinity@ values.
-- To do this, we use the predicate 'isFPPoint', which is true of a floating point
-- number ('SFloat' or 'SDouble') if it is neither @NaN@ nor @Infinity@. (That is, it's a
-- representable point in the real-number line.)
--
-- We have:
--
-- >>> assocPlusRegular
-- Falsifiable. Counter-example:
--   x = 1.5775295e-30 :: SFloat
--   y = 1.92593e-34 :: SFloat
--   z = -2.1521e-41 :: SFloat
--
-- Indeed, we have:
--
-- >>> (1.5775295e-30 + 1.92593e-34) + (-2.1521e-41) :: Float
-- 1.5777222e-30
-- >>> 1.5775295e-30 + (1.92593e-34 + (-2.1521e-41)) :: Float
-- 1.577722e-30
--
-- Note the loss of precision in the second expression.
assocPlusRegular :: IO ThmResult
assocPlusRegular = prove $ do [x, y, z] <- sFloats ["x", "y", "z"]
                              let lhs = x+(y+z)
                                  rhs = (x+y)+z
                              -- make sure we do not overflow at the intermediate points
                              constrain $ isFPPoint lhs
                              constrain $ isFPPoint rhs
                              return $ lhs .== rhs

-----------------------------------------------------------------------------
-- * FP addition by non-zero can result in no change
-----------------------------------------------------------------------------

-- | Demonstrate that @a+b = a@ does not necessarily mean @b@ is @0@ in the floating point world,
-- even when we disallow the obvious solution when @a@ and @b@ are @Infinity.@
-- We have:
--
-- >>> nonZeroAddition
-- Falsifiable. Counter-example:
--   a = -4.0 :: SFloat
--   b = 4.5918e-41 :: SFloat
--
-- Indeed, we have:
--
-- >>> -4.0 + 4.5918e-41 == (-4.0 :: Float)
-- True
--
-- But:
--
-- >>> 4.5918e-41 == (0 :: Float)
-- False
--
nonZeroAddition :: IO ThmResult
nonZeroAddition = prove $ do [a, b] <- sFloats ["a", "b"]
                             constrain $ isFPPoint a
                             constrain $ isFPPoint b
                             constrain $ a + b .== a
                             return $ b .== 0

-----------------------------------------------------------------------------
-- * FP multiplicative inverses may not exist
-----------------------------------------------------------------------------

-- | The last example illustrates that @a * (1/a)@ does not necessarily equal @1@. Again,
-- we protect against division by @0@ and @NaN@/@Infinity@.
--
-- We have:
--
-- >>> multInverse
-- Falsifiable. Counter-example:
--   a = 1.3625818045773776e-308 :: SDouble
--
-- Indeed, we have:
--
-- >>> let a = 1.3625818045773776e-308 :: Double
-- >>> a * (1/a)
-- 0.9999999999999999
multInverse :: IO ThmResult
multInverse = prove $ do a <- sDouble "a"
                         constrain $ isFPPoint a
                         constrain $ isFPPoint (1/a)
                         return $ a * (1/a) .== 1
