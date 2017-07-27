-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Queries.Interpolants
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Demonstrates extraction of interpolants via queries.
-----------------------------------------------------------------------------

module Data.SBV.Examples.Queries.Interpolants where

import Data.SBV
import Data.SBV.Control

-- | Compute the interpolant for formulas @y = 2x@ and @y = 2z+1@.
-- These formulas are not satisfiable together since it would mean
-- @y@ is both even and odd at the same time. An interpolant for
-- this pair of formulas is a formula that's expressed only in terms
-- of @y@, which is the only common symbol among them. We have:
--
-- >>> runSMT evenOdd
-- ["(<= 0 (+ (div s1 2) (div (* (- 1) s1) 2)))"]
--
-- This is a bit hard to read unfortunately, due to translation artifacts and use of strings. To analyze,
-- we need to know that @s1@ is @y@ through SBV's translation. Let's express it in
-- regular infix notation with @y@ for @s1@:
--
-- @ 0 <= (y `div` 2) + ((-y) `div` 2)@
--
-- Notice that the only symbol is @y@, as required. To establish that this is
-- indeed an interpolant, we should establish that when @y@ is even, this formula
-- is @True@; and if @y@ is odd, then then it should be @False@. You can argue
-- mathematically that this indeed the case, but let's just use SBV to prove these:
--
-- >>> prove $ \y -> (y `sMod` 2 .== 0) ==> (0 .<= (y `sDiv` 2) + ((-y) `sDiv` 2::SInteger))
-- Q.E.D.
--
-- And:
--
-- >>> prove $ \y -> (y `sMod` 2 .== 1) ==> bnot (0 .<= (y `sDiv` 2) + ((-y) `sDiv` 2::SInteger))
-- Q.E.D.
--
-- This establishes that we indeed have an interpolant!
evenOdd :: Symbolic [String]
evenOdd = do
       x <- sInteger "x"
       y <- sInteger "y"
       z <- sInteger "z"

       -- tell the solver we want interpolants
       setOption $ ProduceInterpolants True

       -- create named constraints, which will allow
       -- computation of the interpolants for our formulas
       namedConstraint "y is even" $ y .== 2*x
       namedConstraint "y is odd"  $ y .== 2*z + 1

       -- To obtain the interpolant, we run a query
       query $ do cs <- checkSat
                  case cs of
                    Unsat -> getInterpolant ["y is even", "y is odd"]
                    Sat   -> error "Unexpected sat result!"
                    Unk   -> error "Unexpected unknown result!"
