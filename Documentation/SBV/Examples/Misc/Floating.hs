-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Misc.Floating
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Several examples involving IEEE-754 floating point numbers, i.e., single
-- precision 'Float' ('SFloat'), double precision 'Double' ('SDouble'), and
-- the generic 'SFloatingPoint' @eb@ @sb@ type where the user can specify the
-- exponent and significand bit-widths. (Note that there is always an extra
-- sign-bit, and the value of @sb@ includes the hidden bit.)
--
-- Arithmetic with floating point is full of surprises; due to precision
-- issues associativity of arithmetic operations typically do not hold. Also,
-- the presence of @NaN@ is always something to look out for.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Misc.Floating where

import Data.SBV

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV

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
--   x = -1.7478492e-21 :: Float
--   y =   9.693523e-27 :: Float
--   z =   5.595795e-20 :: Float
--
-- Indeed, we have:
--
-- >>> let x = -1.7478492e-21 :: Float
-- >>> let y =   9.693523e-27 :: Float
-- >>> let z =   5.595795e-20 :: Float
-- >>> x + (y + z)
-- 5.4210105e-20
-- >>> (x + y) + z
-- 5.421011e-20
--
-- Note the difference in the results!
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
--   a = 7.135861e-8 :: Float
--   b = 8.57579e-39 :: Float
--
-- Indeed, we have:
--
-- >>> let a = 7.135861e-8 :: Float
-- >>> let b = 8.57579e-39 :: Float
-- >>> a + b == a
-- True
-- >>> b == 0
-- False
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
--   a = -1.4991268e38 :: Float
--
-- Indeed, we have:
--
-- >>> let a = -1.4991268e38 :: Float
-- >>> a * (1/a)
-- 0.99999994
multInverse :: IO ThmResult
multInverse = prove $ do a <- sFloat "a"
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
-- the operation. This example illustrates how SBV can be used to find rounding-modes
-- where, for instance, addition can produce different results. We have:
--
-- >>> roundingAdd
-- Satisfiable. Model:
--   rm = RoundTowardZero :: RoundingMode
--   x  =       1.7499695 :: Float
--   y  =       1.2539366 :: Float
--
-- (Note that depending on your version of Z3, you might get a different result.)
-- Unfortunately Haskell floats do not allow computation with arbitrary rounding modes, but SBV's
-- 'SFloatingPoint' type does. We have:
--
-- >>> sat $ \x -> x .== (fpAdd sRoundTowardZero 1.7499695 1.2539366 :: SFloat)
-- Satisfiable. Model:
--   s0 = 3.003906 :: Float
-- >>> sat $ \x -> x .== (fpAdd sRoundNearestTiesToEven  1.7499695 1.2539366 :: SFloat)
-- Satisfiable. Model:
--   s0 = 3.0039063 :: Float
--
-- We can see why these two results are indeed different: The 'RoundTowardZero'
-- (which rounds towards the origin) produces a smaller result, closer to 0. Indeed, if we treat these numbers
-- as 'Double' values, we get:
--
-- >>>  1.7499695 + 1.2539366 :: Double
-- 3.0039061
--
-- we see that the "more precise" result is smaller than what the 'Float' value is, justifying the
-- smaller value with 'RoundTowardZero. A more detailed study is beyond our current scope, so we'll
-- merely note that floating point representation and semantics is indeed a thorny
-- subject, and point to <http://ece.uwaterloo.ca/~dwharder/NumericalAnalysis/02Numerics/Double/paper.pdf> as
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

-- | Arbitrary precision floating-point numbers. SBV can talk about floating point numbers with arbitrary
-- exponent and significand sizes as well. Here is a simple example demonstrating the minimum non-zero positive
-- and maximum floating point values with exponent width 5 and significand width 4, which is actually 3
-- bits for the significand explicitly stored, includes the hidden bit. We have:
--
-- >>> fp54Bounds
-- Objective "max": Optimal model:
--   x   = 61440 :: FloatingPoint 5 4
--   max =   503 :: WordN 9
--   min =   503 :: WordN 9
-- Objective "min": Optimal model:
--   x   = 0.000007629 :: FloatingPoint 5 4
--   max =         257 :: WordN 9
--   min =         257 :: WordN 9
--
-- An important note is in order. When printing floats in decimal, one can get correct yet surprising results.
-- There's a large body of publications in how to render floats in decimal, or in bases that are not powers of
-- two in general. So, when looking at such values in decimal, keep in mind that what you see might be
-- a representative value: That is, it preserves the value when translated back to the format. For instance,
-- the more precise answer for the min value would be 2^-17, which is 0.00000762939453125. But we see
-- it truncated here. In fact, any number between 2^-16 and 2^-17 would be correct as they all map to the same
-- underlying representation in this format. Moral of the story is that when reading floating-point numbers in
-- decimal notation one should be very careful about the printed representation and the numeric value; while
-- they will match in value (if there are no bugs!), they can print quite differently! (Also keep in
-- mind the rounding modes that impact how the conversion is done.)
fp54Bounds :: IO OptimizeResult
fp54Bounds = optimize Independent $ do x :: SFloatingPoint 5 4 <- sFloatingPoint "x"

                                       constrain $ fpIsPoint x
                                       constrain $ x .> 0

                                       maximize "max" x
                                       minimize "min" x

                                       pure sTrue
