-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Uninterpreted.Deduce
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrates uninterpreted sorts and how they can be used for deduction.
-- This example is inspired by the discussion at <http://stackoverflow.com/questions/10635783/using-axioms-for-deductions-in-z3>,
-- essentially showing how to show the required deduction using SBV.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Uninterpreted.Deduce where

import Data.SBV

-- we will have our own "uninterpreted" functions corresponding
-- to not/or/and, so hide their Prelude counterparts.
import Prelude hiding (not, or, and)

-----------------------------------------------------------------------------
-- * Representing uninterpreted booleans
-----------------------------------------------------------------------------

-- | The uninterpreted sort 'B', corresponding to the carrier.
data B

-- | Make this sort uninterpreted. This splice will automatically introduce
-- the type 'SB' into the environment, as a synonym for 'SBV' 'B'.
mkUninterpretedSort ''B

-----------------------------------------------------------------------------
-- * Uninterpreted connectives over 'B'
-----------------------------------------------------------------------------

-- | Uninterpreted logical connective 'and'
and :: SB -> SB -> SB
and = uninterpret "AND"

-- | Uninterpreted logical connective 'or'
or :: SB -> SB -> SB
or  = uninterpret "OR"

-- | Uninterpreted logical connective 'not'
not :: SB -> SB
not = uninterpret "NOT"

-----------------------------------------------------------------------------
-- * Demonstrated deduction
-----------------------------------------------------------------------------

-- | Proves the equivalence @NOT (p OR (q AND r)) == (NOT p AND NOT q) OR (NOT p AND NOT r)@,
-- following from the axioms we have specified above. We have:
--
-- >>> test
-- Q.E.D.
test :: IO ThmResult
test = prove $ do constrain $ \(Forall p) (Forall q) (Forall r) -> (p `or` q) `and` (p `or` r) .== p `or` (q `and` r)
                  constrain $ \(Forall p) (Forall q)            -> not (p `or` q) .== not p `and` not q
                  constrain $ \(Forall p)                       -> not (not p) .== p
                  p <- free "p"
                  q <- free "q"
                  r <- free "r"
                  return $   not (p `or` (q `and` r))
                         .== (not p `and` not q) `or` (not p `and` not r)

-- Hlint gets confused and thinks the use of @not@ above is from the prelude. Sigh.
{- HLint ignore test "Redundant not" -}
