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

{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Examples.Misc.Floating where

import Data.SBV

-----------------------------------------------------------------------------
-- * FP addition is not associative
-----------------------------------------------------------------------------

-- | Prove that floating point addition is not associative. We have:
--
-- >>> prove assocPlus
-- Falsifiable. Counter-example:
--   s0 = -7.888609e-31 :: SFloat
--   s1 = 3.944307e-31 :: SFloat
--   s2 = NaN :: SFloat
--
-- Indeed:
--
-- >>> let i = 0/0 :: Float
-- >>> ((-7.888609e-31 + 3.944307e-31) + i) :: Float
-- NaN
-- >>> (-7.888609e-31 + (3.944307e-31 + i)) :: Float
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
--   x = -3.7777752e22 :: SFloat
--   y = -1.180801e18 :: SFloat
--   z = 9.4447324e21 :: SFloat
--
-- Indeed, we have:
--
-- >>> ((-3.7777752e22 + (-1.180801e18)) + 9.4447324e21) :: Float
-- -2.83342e22
-- >>> (-3.7777752e22 + ((-1.180801e18) + 9.4447324e21)) :: Float
-- -2.8334201e22
--
-- Note the loss of precision in the first expression.
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
--   a = 2.1474839e10 :: SFloat
--   b = -7.275957e-11 :: SFloat
--
-- Indeed, we have:
--
-- >>> 2.1474839e10 + (-7.275957e-11) == (2.1474839e10 :: Float)
-- True
--
-- But:
--
-- >>> -7.275957e-11 == (0 :: Float)
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

-- | This example illustrates that @a * (1/a)@ does not necessarily equal @1@. Again,
-- we protect against division by @0@ and @NaN@/@Infinity@.
--
-- We have:
--
-- >>> multInverse
-- Falsifiable. Counter-example:
--   a = 1.2354518252390238e308 :: SDouble
--
-- Indeed, we have:
--
-- >>> let a = 1.2354518252390238e308 :: Double
-- >>> a * (1/a)
-- 0.9999999999999998
multInverse :: IO ThmResult
multInverse = prove $ do a <- sDouble "a"
                         constrain $ isFPPoint a
                         constrain $ isFPPoint (1/a)
                         return $ a * (1/a) .== 1

-----------------------------------------------------------------------------
-- * Effect of rounding modes
-----------------------------------------------------------------------------

-- | One interesting aspect of floating-point is that the chosen rounding-mode
-- can effect the results of a computation if the exact result cannot be precisely
-- represented. SBV exports the functions 'fpAdd', 'fpSub', 'fpMul', 'fpDiv', 'fpFMA'
-- and 'fpSqrt' which allows users to specify the IEEE supported 'RoundingMode' for
-- the operation. (Also see the class 'RoundingFloat'.) This example illustrates how SBV
-- can be used to find rounding-modes where, for instance, addition can produce different
-- results. We have:
--
-- >>> roundingAdd
-- Satisfiable. Model:
--   rm = RoundTowardPositive :: RoundingMode
--   x = 1.7014118e38 :: SFloat
--   y = 1.1754942e-38 :: SFloat
--
-- Unfortunately we can't directly validate this result at the Haskell level, as Haskell only supports
-- 'RoundNearestTiesToEven'. We have:
--
-- >>> (1.7014118e38 + 1.1754942e-38) :: Float
-- 1.7014118e38
--
-- Note that result is identical to the first argument. But with a 'RoundTowardPositive', we would
-- get the result @1.701412e38@. While we cannot directly see this from within Haskell, we can
-- use SBV to provide us with that result thusly:
--
-- >>> sat $ \x -> x .== fpAdd (literal RoundTowardPositive) (1.7014118e38::SFloat)  (1.1754942e-38::SFloat)
-- Satisfiable. Model:
--   s0 = 1.701412e38 :: SFloat
--
-- We can see why these two resuls are different if we treat these values as arbitrary
-- precision reals, as represented by the 'SReal' type:
--
-- >>> let x = 1.7014118e38 :: SReal
-- >>> let y = 1.1754942e-38 :: SReal
-- >>> x
-- 170141180000000000000000000000000000000.0 :: SReal
-- >>> y
-- 0.000000000000000000000000000000000000011754942 :: SReal
-- >>> x + y
-- 170141180000000000000000000000000000000.000000000000000000000000000000000000011754942 :: SReal
--
-- When we do 'RoundNearestTiesToEven', the entire suffix falls off, as it happens that the infinitely
-- precise result is closer to the value of @x@. But when we use 'RoundTowardPositive', we reach
-- for the next representable number, which happens to be @1.701412e38@. You might wonder why not
-- @1.7014119e38@? Because that number is not precisely representable as a 'Float':
--
-- >>> 1.7014119e38:: Float
-- 1.7014118e38
--
-- But @1.701412e38@ is:
--
-- >>> 1.701412e38 :: Float
-- 1.701412e38
--
-- Floating point representation and semantics is indeed a thorny subject, <https://ece.uwaterloo.ca/~dwharder/NumericalAnalysis/02Numerics/Double/paper.pdf> happens to be an excellent guide, however.
roundingAdd :: IO SatResult
roundingAdd = sat $ do m :: SRoundingMode <- free "rm"
                       x <- sFloat "x"
                       y <- sFloat "y"
                       constrain $ m ./= literal RoundNearestTiesToEven
                       return $ fpAdd m x y ./= x + y
