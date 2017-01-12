-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Uninterpreted.Sort
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Demonstrates uninterpreted sorts, together with axioms.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Data.SBV.Examples.Uninterpreted.Sort where

import Data.Generics
import Data.SBV

-- | A new data-type that we expect to use in an uninterpreted fashion
-- in the backend SMT solver. Note the custom @deriving@ clause, which
-- takes care of most of the boilerplate. The () field is needed so
-- SBV will not translate it to an enumerated data-type
newtype Q = Q () deriving (Eq, Ord, Data, Read, Show, SymWord, HasKind)

-- | Declare an uninterpreted function that works over Q's
f :: SBV Q -> SBV Q
f = uninterpret "f"

-- | A satisfiable example, stating that there is an element of the domain
-- 'Q' such that 'f' returns a different element. Note that this is valid only
-- when the domain 'Q' has at least two elements. We have:
--
-- >>> t1
-- Satisfiable. Model:
--   x = Q!val!0 :: Q
t1 :: IO SatResult
t1 = sat $ do x <- free "x"
              return $ f x ./= x

-- | This is a variant on the first example, except we also add an axiom
-- for the sort, stating that the domain 'Q' has only one element. In this case
-- the problem naturally becomes unsat. We have:
--
-- >>> t2
-- Unsatisfiable
t2 :: IO SatResult
t2 = sat $ do x <- free "x"
              addAxiom "Q" ["(assert (forall ((x Q) (y Q)) (= x y)))"]
              return $ f x ./= x
