-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Queries.Interpolants
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrates extraction of interpolants via queries.
--
-- N.B. Interpolants are supported by MathSAT and Z3. Unfortunately
-- the extraction of interpolants is not standardized, and are slightly
-- different for these two solvers. So, we have two separate examples
-- to demonstrate the usage.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Queries.Interpolants where

import Data.SBV
import Data.SBV.Control

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV
-- >>> import Data.SBV.Control

-- | MathSAT example. Compute the interpolant for the following sets of formulas:
--
--     @{x - 3y >= -1, x + y >= 0}@
--
-- AND
--
--     @{z - 2x >= 3, 2z <= 1}@
--
-- where the variables are integers.  Note that these sets of
-- formulas are themselves satisfiable, but not taken all together.
-- The pair @(x, y) = (0, 0)@ satisfies the first set. The pair @(x, z) = (-2, 0)@
-- satisfies the second. However, there's no triple @(x, y, z)@ that satisfies all
-- these four formulas together. We can use SBV to check this fact:
--
-- >>> sat $ \x y z -> sAnd [x - 3*y .>= -1, x + y .>= 0, z - 2*x .>= 3, 2 * z .<= (1::SInteger)]
-- Unsatisfiable
--
-- An interpolant for these sets would only talk about the variable @x@ that is common
-- to both. We have:
--
-- >>> runSMTWith mathSAT exampleMathSAT
-- "(<= 0 s0)"
--
-- Notice that we get a string back, not a term; so there's some back-translation we need to do. We
-- know that @s0@ is @x@ through our translation mechanism, so the interpolant is saying that @x >= 0@
-- is entailed by the first set of formulas, and is inconsistent with the second. Let's use SBV
-- to indeed show that this is the case:
--
-- >>> prove $ \x y -> (x - 3*y .>= -1 .&& x + y .>= 0) .=> (x .>= (0::SInteger))
-- Q.E.D.
--
-- And:
--
-- >>> prove $ \x z -> (z - 2*x .>= 3 .&& 2 * z .<= 1) .=> sNot (x .>= (0::SInteger))
-- Q.E.D.
--
-- This establishes that we indeed have an interpolant!
exampleMathSAT :: Symbolic String
exampleMathSAT = do
       x <- sInteger "x"
       y <- sInteger "y"
       z <- sInteger "z"

       -- tell the solver we want interpolants
       -- NB. Only MathSAT needs this. Z3 doesn't need or like this setting!
       setOption $ ProduceInterpolants True

       -- create interpolation constraints. MathSAT requires the relevant formulas
       -- to be marked with the attribute :interpolation-group
       constrainWithAttribute [(":interpolation-group", "A")] $ x - 3*y .>= -1
       constrainWithAttribute [(":interpolation-group", "A")] $ x + y   .>=  0
       constrainWithAttribute [(":interpolation-group", "B")] $ z - 2*x .>=  3
       constrainWithAttribute [(":interpolation-group", "B")] $ 2*z     .<=  1

       -- To obtain the interpolant, we run a query
       query $ do cs <- checkSat
                  case cs of
                    Unsat  -> getInterpolantMathSAT ["A"]
                    DSat{} -> error "Unexpected delta-sat result!"
                    Sat    -> error "Unexpected sat result!"
                    Unk    -> error "Unexpected unknown result!"

-- | Z3 example. Compute the interpolant for formulas @y = 2x@ and @y = 2z+1@.
--
-- These formulas are not satisfiable together since it would mean
-- @y@ is both even and odd at the same time. An interpolant for
-- this pair of formulas is a formula that's expressed only in terms
-- of @y@, which is the only common symbol among them. We have:
--
-- >>> runSMT evenOdd
-- "(let (a!1 (= (mod (+ (* (- 1) s1) 0) 2) 0)) (or (= s1 0) a!1))"
--
-- This is a bit hard to read unfortunately, due to translation artifacts and use of strings. To analyze,
-- we need to know that @s1@ is @y@ through SBV's translation. Let's express it in
-- regular infix notation with @y@ for @s1@, and substitute the let-bound variable:
--
-- @(y == 0) || ((-y) `mod` 2 == 0)@
--
-- Notice that the only symbol is @y@, as required. To establish that this is
-- indeed an interpolant, we should establish that when @y@ is even, this formula
-- is @True@; and if @y@ is odd, then it should be @False@. You can argue
-- mathematically that this indeed the case, but let's just use SBV to prove the required relationships:
--
-- >>> prove $ \(y :: SInteger) -> (y `sMod` 2 .== 0) .=> ((y .== 0) .|| ((-y) `sMod` 2 .== 0))
-- Q.E.D.
--
-- And:
--
-- >>> prove $ \(y :: SInteger) -> (y `sMod` 2 .== 1) .=> sNot ((y .== 0) .|| ((-y) `sMod` 2 .== 0))
-- Q.E.D.
--
-- This establishes that we indeed have an interpolant!
evenOdd :: Symbolic String
evenOdd = do
       x <- sInteger "x"
       y <- sInteger "y"
       z <- sInteger "z"

       query $ getInterpolantZ3 [y .== 2*x, y .== 2*z+1]

{- HLint ignore module "Reduce duplication" -}
