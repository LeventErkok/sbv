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

module Documentation.SBV.Examples.Uninterpreted.Deduce where

import Data.Generics
import Data.SBV

-- we will have our own "uninterpreted" functions corresponding
-- to not/or/and, so hide their Prelude counterparts.
import Prelude hiding (not, or, and)

-----------------------------------------------------------------------------
-- * Representing uninterpreted booleans
-----------------------------------------------------------------------------

-- | The uninterpreted sort 'B', corresponding to the carrier.
-- To prevent SBV from translating it to an enumerated type, we simply attach an unused field
newtype B = B () deriving (Eq, Ord, Show, Read, Data, SymVal, HasKind)

-- | Handy shortcut for the type of symbolic values over 'B'
type SB = SBV B

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
-- * Axioms of the logical system
-----------------------------------------------------------------------------

-- | Distributivity of OR over AND, as an axiom in terms of
-- the uninterpreted functions we have introduced. Note how
-- variables range over the uninterpreted sort 'B'.
ax1 :: [String]
ax1 = [ "(assert (forall ((p B) (q B) (r B))"
      , "   (= (AND (OR p q) (OR p r))"
      , "      (OR p (AND q r)))))"
      ]

-- | One of De Morgan's laws, again as an axiom in terms
-- of our uninterpeted logical connectives.
ax2 :: [String]
ax2 = [ "(assert (forall ((p B) (q B))"
      , "   (= (NOT (OR p q))"
      , "      (AND (NOT p) (NOT q)))))"
      ]

-- | Double negation axiom, similar to the above.
ax3 :: [String]
ax3 = ["(assert (forall ((p B)) (= (NOT (NOT p)) p)))"]

-----------------------------------------------------------------------------
-- * Demonstrated deduction
-----------------------------------------------------------------------------

-- | Proves the equivalence @NOT (p OR (q AND r)) == (NOT p AND NOT q) OR (NOT p AND NOT r)@,
-- following from the axioms we have specified above. We have:
--
-- >>> test
-- Q.E.D.
test :: IO ThmResult
test = prove $ do addAxiom "OR distributes over AND" ax1
                  addAxiom "de Morgan"               ax2
                  addAxiom "double negation"         ax3
                  p <- free "p"
                  q <- free "q"
                  r <- free "r"
                  return $   not (p `or` (q `and` r))
                         .== (not p `and` not q) `or` (not p `and` not r)
