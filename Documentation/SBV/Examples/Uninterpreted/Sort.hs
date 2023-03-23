-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Uninterpreted.Sort
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrates uninterpreted sorts, together with axioms.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Uninterpreted.Sort where

import Data.SBV

-- | A new data-type that we expect to use in an uninterpreted fashion
-- in the backend SMT solver.
data Q

-- | Make 'Q' an uinterpreted sort. This will automatically introduce the
-- type 'SQ' into our environment, which is the symbolic version of the
-- carrier type 'Q'.
mkUninterpretedSort ''Q

-- | Declare an uninterpreted function that works over Q's
f :: SQ -> SQ
f = uninterpret "f"

-- | A satisfiable example, stating that there is an element of the domain
-- 'Q' such that 'f' returns a different element. Note that this is valid only
-- when the domain 'Q' has at least two elements. We have:
--
-- >>> t1
-- Satisfiable. Model:
--   x = Q!val!0 :: Q
-- <BLANKLINE>
--   f :: Q -> Q
--   f _ = Q!val!1
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
              constrain $ \(Forall a) (Forall b) -> a .== (b :: SQ)
              return $ f x ./= x
