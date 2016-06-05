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

-- | Prove that floating point addition is not associative. For illustration purposes,
-- we will require one of the inputs to be a @NaN@. We have:
--
-- >>> prove $ assocPlus (0/0)
-- Falsifiable. Counter-example:
--   s0 = 0.0 :: Float
--   s1 = 0.0 :: Float
--
-- Indeed:
--
-- >>> let i = 0/0 :: Float
-- >>> i + (0.0 + 0.0)
-- NaN
-- >>> ((i + 0.0) + 0.0)
-- NaN
--
-- But keep in mind that @NaN@ does not equal itself in the floating point world! We have:
--
-- >>> let nan = 0/0 :: Float in nan == nan
-- False
assocPlus :: SFloat -> SFloat -> SFloat -> SBool
assocPlus x y z = x + (y + z) .== (x + y) + z

-- | Prove that addition is not associative, even if we ignore @NaN@/@Infinity@ values.
-- To do this, we use the predicate 'fpIsPoint', which is true of a floating point
-- number ('SFloat' or 'SDouble') if it is neither @NaN@ nor @Infinity@. (That is, it's a
-- representable point in the real-number line.)
--
-- We have:
--
-- >>> assocPlusRegular
-- Falsifiable. Counter-example:
--   x =  5.5511693e-15 :: Float
--   y = -2.2204438e-16 :: Float
--   z = -3.1763606e-21 :: Float
--
-- Indeed, we have:
--
-- >>> ((5.5511693e-15) + ((-2.2204438e-16) + (-3.1763606e-21))) :: Float
-- 5.3291218e-15
-- >>> (((5.5511693e-15) + (-2.2204438e-16)) + (-3.1763606e-21)) :: Float
-- 5.329122e-15
--
-- Note the difference between two additions!
assocPlusRegular :: IO ThmResult
assocPlusRegular = prove $ do [x, y, z] <- sFloats ["x", "y", "z"]
                              let lhs = x+(y+z)
                                  rhs = (x+y)+z
                              -- make sure we do not overflow at the intermediate points
                              constrain $ fpIsPoint lhs
                              constrain $ fpIsPoint rhs
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
--   a =  5.1705105e-26 :: Float
--   b = -3.8518597e-34 :: Float
--
-- Indeed, we have:
--
-- >>> (5.1705105e-26 + (-3.8518597e-34)) == (5.1705105e-26 :: Float)
-- True
--
-- But:
--
-- >>> -3.8518597e-34 == (0::Float)
-- False
--
nonZeroAddition :: IO ThmResult
nonZeroAddition = prove $ do [a, b] <- sFloats ["a", "b"]
                             constrain $ fpIsPoint a
                             constrain $ fpIsPoint b
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
--   a = 8.988465674311586e307 :: Double
--
-- Indeed, we have:
--
-- >>> let a = 8.988465674311586e307 :: Double
-- >>> a * (1/a)
-- 1.0000000000000002
multInverse :: IO ThmResult
multInverse = prove $ do a <- sDouble "a"
                         constrain $ fpIsPoint a
                         constrain $ fpIsPoint (1/a)
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
--   x  =           1.9531249 :: Float
--   y  =        6.2499996e-2 :: Float
--
-- (Note that depending on your version of Z3, you might get a different result.)
-- Unfortunately we can't directly validate this result at the Haskell level, as Haskell only supports
-- 'RoundNearestTiesToEven'. We have:
--
-- >>> (1.9531249 + 6.2499996e-2) :: Float
-- 2.0156248
--
-- While we cannot directly see the result when the mode is 'RoundTowardPositive' in Haskell, we can use
-- SBV to provide us with that result thusly:
--
-- >>> sat $ \z -> z .== fpAdd sRoundTowardPositive 1.9531249 (6.2499996e-2 :: SFloat)
-- Satisfiable. Model:
--   s0 = 2.015625 :: Float
--
-- We can see why these two resuls are indeed different. But we can see that the 'RoundTowardsPositive'
-- (which rounds towards positive-infinity) produces a larger result. Indeed, if we treat these numbers
-- as 'Double' values, we get:
--
-- >>>  (1.9531249 + 6.2499996e-2) :: Double
-- 2.015624896
--
-- we see that the "more precise" result is larger than what the 'Float' value is, justifying the
-- larger value with 'RoundTowardPositive'. A more detailed study is beyond our current scope, so we'll
--  merely -- note that floating point representation and semantics is indeed a thorny
-- subject, and point to <https://ece.uwaterloo.ca/~dwharder/NumericalAnalysis/02Numerics/Double/paper.pdf> as
-- an excellent guide.
roundingAdd :: IO SatResult
roundingAdd = sat $ do m :: SRoundingMode <- free "rm"
                       constrain $ m ./= literal RoundNearestTiesToEven
                       x <- sFloat "x"
                       y <- sFloat "y"
                       let lhs = fpAdd m x y
                       let rhs = x + y
                       constrain $ fpIsPoint lhs
                       constrain $ fpIsPoint rhs
                       return $ lhs ./= rhs
