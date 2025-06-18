-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.RevAcc
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proves that the accummulating version of reverse is equivalent to the
-- standard definition.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.RevAcc where

import Prelude hiding (head, tail, null, reverse, (++))

import Data.SBV
import Data.SBV.List
import Data.SBV.TP

#ifdef DOCTEST
-- $setup
-- >>> :set -XTypeApplications
#endif

-- * Reversing with an accummulator.

-- | Accummulating reverse.
revAcc :: SymVal a => SList a -> SList a -> SList a
revAcc = smtFunction "revAcc" $ \acc xs -> ite (null xs) acc (revAcc (head xs .: acc) (tail xs))

-- | Given 'revAcc', we can reverse a list by providing the empty list as the initial accumulator.
rev :: SymVal a => SList a -> SList a
rev = revAcc []

-- * Correctness proof

-- | Correctness the function 'rev'. We have:
--
-- >>> correctness @Integer
-- Inductive lemma: revAccCorrect
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: revCorrect                       Q.E.D.
-- [Proven] revCorrect :: Ɐxs ∷ [Integer] → Bool
correctness :: forall a. SymVal a => IO (Proof (Forall "xs" [a] -> SBool))
correctness = runTP $ do

  -- Helper lemma regarding 'revAcc'
  helper <- induct "revAccCorrect"
                   (\(Forall @"xs" (xs :: SList a)) (Forall @"acc" acc) -> revAcc acc xs .== reverse xs ++ acc) $
                   \ih (x, xs) acc -> [] |- revAcc acc (x .: xs)
                                         =: revAcc (x .: acc) xs
                                         ?? ih
                                         =: reverse xs ++ x .: acc
                                         =: (reverse xs ++ [x]) ++ acc
                                         =: reverse (x .: xs) ++ acc
                                         =: qed

  -- The main theorem simply follows from the helper:
  lemma "revCorrect"
        (\(Forall xs) -> rev xs .== reverse xs)
        [proofOf helper]
