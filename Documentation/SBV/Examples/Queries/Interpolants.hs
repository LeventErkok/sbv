-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Queries.Interpolants
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrates extraction of interpolants via queries.
--
-- N.B. As of Z3 version 4.8.0; Z3 no longer supports interpolants. You need
-- to use the MathSAT backend for this example to work.
-----------------------------------------------------------------------------

module Documentation.SBV.Examples.Queries.Interpolants where

import Data.SBV
import Data.SBV.Control

-- | Compute the interpolant for the following sets of formulas:
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
-- >>> runSMTWith mathSAT example
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
example :: Symbolic String
example = do
       x <- sInteger "x"
       y <- sInteger "y"
       z <- sInteger "z"

       -- tell the solver we want interpolants
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
                    Unsat -> getInterpolant ["A"]
                    Sat   -> error "Unexpected sat result!"
                    Unk   -> error "Unexpected unknown result!"
