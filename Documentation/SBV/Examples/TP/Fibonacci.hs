-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Fibonacci
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving that the naive version of fibonacci and the faster tail-recursive
-- version are equivalent.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Fibonacci(correctness) where

import Data.SBV
import Data.SBV.TP

-- * Naive fibonacci

-- | Calculate fibonacci using the textbook definition.
fibonacci :: SInteger -> SInteger
fibonacci = smtFunction "fibonacci" $ \n -> ite (n .<= 1) 1 (fibonacci (n-1) + fibonacci (n-2))

-- * Tail recursive version

-- | Tail recursive version
fib :: SInteger -> SInteger -> SInteger -> SInteger
fib = smtFunction "fib" $ \a b n -> ite (n .<= 0) a (fib b (a+b) (n-1))

-- | Faster version of fibonacci, using the tail-recursive version.
fibTail :: SInteger -> SInteger
fibTail = fib 1 1

-- * Correctness

-- | Proving the the tail version of fibonacci is equivalent to the textbook version.
--
-- We have:
--
-- >>> correctness
-- Inductive lemma: helper
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2 (unfold fibonacci)            Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: fibCorrect
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] fibCorrect
correctness :: IO (Proof (Forall "n" Integer -> SBool))
correctness = runTP $ do

  helper <- induct "helper"
                   (\(Forall @"n" n) (Forall @"k" k) ->
                       n .>= 0 .&& k .>= 0 .=> fib (fibonacci k) (fibonacci (k+1)) n .== fibonacci (k+n)) $
                   \ih (n, k) -> [n .>= 0, k .>= 0]
                              |- fib (fibonacci k) (fibonacci (k+1)) (n+1)
                              =: fib (fibonacci (k+1)) (fibonacci k + fibonacci (k+1)) n
                              ?? "unfold fibonacci"
                              =: fib (fibonacci (k+1)) (fibonacci (k+2)) n
                              ?? ih `at` Inst @"k" (k+1)
                              =: fibonacci (k+1+n)
                              =: qed

  calc "fibCorrect"
       (\(Forall n) -> n .>= 0 .=> fibonacci n .== fibTail n) $
       \n -> [n .>= 0] |- fibTail n
                       =: fib 1 1 n
                       ?? helper `at` (Inst @"n" n, Inst @"k" (0 :: SInteger))
                       =: fibonacci n
                       =: qed
