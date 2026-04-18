-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Collatz
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- The Collatz function: starting from a positive integer, if it is 1 we stop;
-- if it is even we halve it; if it is odd we triple and add one.  Whether this
-- process terminates for every positive integer is the famous Collatz conjecture,
-- an open problem in mathematics. Because no termination measure is known, we
-- define 'collatz' with 'smtFunctionNoTermination', which emits the recursive
-- definition without any termination check.
--
-- We then prove that 'collatz' reaches 1 for every power of two.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Collatz where

import Data.SBV
import Data.SBV.TP

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV.TP
#endif

-- * Definitions

-- | The Collatz function. Termination for all positive integers is the famous
-- Collatz conjecture, an open problem in mathematics. We use 'smtFunctionNoTermination'
-- since no termination measure is known.
collatz :: SInteger -> SInteger
collatz = smtFunctionNoTermination "collatz"
        $ \n -> [sCase| n of
                   1                  -> 1
                   _ | 2 `sDivides` n -> collatz (n `sDiv` 2)
                     | True           -> collatz (3 * n + 1)
                |]

-- | Power of two: @pow2 k = 2^k@ for @k >= 0@.
pow2 :: SInteger -> SInteger
pow2 = smtFunction "pow2"
     $ \k -> [sCase| k of
                _ | k .<= 0 -> 1
                  | True    -> 2 * pow2 (k - 1)
             |]

-- * Helper lemmas

-- | Doubling doesn't change the Collatz result.
--
-- >>> runTP doubling
-- Lemma: doubling    Q.E.D. [Modulo: collatz termination]
-- [Modulo: collatz termination] doubling :: Ɐn ∷ Integer → Bool
doubling :: TP (Proof (Forall "n" Integer -> SBool))
doubling = lemma "doubling" (\(Forall @"n" n) -> n .>= 1 .=> collatz (2 * n) .== collatz n) []

-- | Powers of two are positive.
--
-- >>> runTP pow2pos
-- Inductive lemma: pow2pos
--   Step: Base                Q.E.D.
--   Step: 1                   Q.E.D.
--   Step: 2                   Q.E.D.
--   Result:                   Q.E.D.
-- Functions proven terminating: pow2
-- [Proven] pow2pos :: Ɐk ∷ Integer → Bool
pow2pos :: TP (Proof (Forall "k" Integer -> SBool))
pow2pos = induct "pow2pos"
                 (\(Forall @"k" k) -> pow2 k .>= 1) $
                 \ih k -> []
                       |- pow2 (k + 1) .>= 1
                       =: 2 * pow2 k .>= 1
                       ?? ih
                       =: sTrue
                       =: qed

-- * Correctness

-- | All powers of two reach 1 under the Collatz function.
--
-- >>> runTP collatzPow2
-- Lemma: doubling                 Q.E.D. [Modulo: collatz termination]
-- Lemma: pow2pos                  Q.E.D.
-- Inductive lemma: collatzPow2
--   Step: Base                    Q.E.D.
--   Step: 1                       Q.E.D.
--   Step: 2                       Q.E.D. [Modulo: collatz termination]
--   Step: 3                       Q.E.D.
--   Result:                       Q.E.D. [Modulo: collatz termination]
-- Functions proven terminating: pow2
-- [Modulo: collatz termination] collatzPow2 :: Ɐk ∷ Integer → Bool
collatzPow2 :: TP (Proof (Forall "k" Integer -> SBool))
collatzPow2 = do
   dbl <- recall doubling
   p2p <- recall pow2pos

   induct "collatzPow2"
          (\(Forall @"k" k) -> k .>= 0 .=> collatz (pow2 k) .== 1) $
          \ih k -> [k .>= 0]
                |- collatz (pow2 (k + 1))
                =: collatz (2 * pow2 k)
                ?? dbl
                ?? p2p
                =: collatz (pow2 k)
                ?? ih
                =: (1 :: SInteger)
                =: qed
