-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Productive
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrating productive (corecursive) functions.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Productive where

import Prelude hiding (head, length, (!!))

import Data.SBV
import Data.SBV.List
import Data.SBV.TP

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV.TP
#endif

-- * Definitions

-- | A productive function that counts down from @n@ to @0@. Every recursive call is
-- guarded by a list constructor (@.:@), so SBV accepts it as productive without
-- requiring a termination measure.
countdown :: SInteger -> SList Integer
countdown = smtProductiveFunction "countdown" $ \n -> [sCase| n of
                                                         v | v .<= 0 -> singleton 0
                                                           | True    -> v .: countdown (v - 1)
                                                      |]

-- * Correctness

-- | Prove that @countdown n@ always starts with @n@, for positive @n@.
--
-- >>> runTP countdownHead
-- Lemma: countdownHead                    Q.E.D.
-- Functions proven productive: countdown
-- [Proven] countdownHead :: Ɐn ∷ Integer → Bool
countdownHead :: TP (Proof (Forall "n" Integer -> SBool))
countdownHead = lemma "countdownHead" (\(Forall @"n" n) -> n .> 0 .=> head (countdown n) .== n) []

-- | Prove by induction that @countdown n@ is never empty.
--
-- >>> runTP countdownNonEmpty
-- Inductive lemma: countdownNonEmpty
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- Functions proven productive: countdown
-- [Proven] countdownNonEmpty :: Ɐn ∷ Integer → Bool
countdownNonEmpty :: TP (Proof (Forall "n" Integer -> SBool))
countdownNonEmpty =
   induct "countdownNonEmpty"
          (\(Forall @"n" n) -> n .>= 0 .=> length (countdown n) .> 0) $
          \ih n -> [n .>= 0] |- length (countdown (n + 1))
                             =: length ((n + 1) .: countdown n)
                             ?? ih
                             =: 1 + length (countdown n)
                             =: qed

-- | Prove by induction that @countdown n@ has length @n + 1@.
--
-- >>> runTP countdownLen
-- Inductive lemma: countdownLen
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Functions proven productive: countdown
-- [Proven] countdownLen :: Ɐn ∷ Integer → Bool
countdownLen :: TP (Proof (Forall "n" Integer -> SBool))
countdownLen =
   induct "countdownLen"
          (\(Forall @"n" n) -> n .>= 0 .=> length (countdown n) .== n + 1) $
          \ih n -> [n .>= 0] |- length (countdown (n + 1))
                             =: length ((n + 1) .: countdown n)
                             =: 1 + length (countdown n)
                             ?? ih
                             =: n + 2
                             =: qed

-- | Prove by induction that the @k@-th element of @countdown n@ is @n - k@.
--
-- The key subtlety is that the 'induct' Result step only has access to the calc chain
-- equalities, not to the helper proofs (which live inside each step's assertion stack).
-- The Result step must prove @P(n+1, k)@ for all valid @k@, i.e., @0 <= k <= n+1@.
-- If the intros only cover @k <= n@, the Result step has no information for @k = n+1@
-- and hangs. The fix is to use intros @[n >= 0, 0 <= k, k <= n+1]@ so the calc chain
-- covers the entire domain of the goal.
--
-- >>> runTP countdownElem
-- Lemma: countdownLen                     Q.E.D.
-- Lemma: elemOne                          Q.E.D.
-- Inductive lemma: countdownElem
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- Functions proven productive: countdown
-- [Proven] countdownElem :: Ɐn ∷ Integer → Ɐk ∷ Integer → Bool
countdownElem :: TP (Proof (Forall "n" Integer -> Forall "k" Integer -> SBool))
countdownElem = do
   cLen <- recall "countdownLen" countdownLen

   -- NB. The precondition uses (<=) not (<): this is important so the lemma covers
   -- k = length y (the last valid index of x .: y), not just k < length y.
   elemOne <- lemma "elemOne" (\(Forall @"x" (x :: SInteger)) (Forall @"y" y) (Forall @"k" k) ->
                                   k .> 0 .&& k .<= length y .=> (x .: y) !! k .== y !! (k - 1)) []

   induct "countdownElem"
          (\(Forall @"n" n) (Forall @"k" k) -> 0 .<= k .&& k .<= n .=> countdown n !! k .== n - k) $
          \ih n k -> [n .>= 0, 0 .<= k, k .<= n + 1]
                  |- countdown (n + 1) !! k
                  =: ((n + 1) .: countdown n) !! k
                  ?? elemOne
                  ?? cLen
                  ?? ih `at` Inst @"k" (k - 1)
                  =: n + 1 - k
                  =: qed
