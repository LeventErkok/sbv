-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.MutualCorecursion
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrating mutually corecursive (productive) functions. Two functions
-- @ping@ and @pong@ take turns producing elements of a stream: each emits
-- its argument and then calls the other with the next value:
--
-- @
--   ping n = n .: pong (n + 1)
--   pong n = n .: ping (n + 1)
-- @
--
-- Together they produce the natural number stream starting from @n@:
-- @ping 0 = [0, 1, 2, 3, ...]@. We prove that the @k@-th element
-- of @ping n@ is @n + k@.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.MutualCorecursion where

import Prelude hiding (head, length, (!!))

import Data.SBV
import Data.SBV.List
import Data.SBV.TP

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV.TP
#endif

-- * Definitions

-- | @ping n@ emits @n@ and hands off to 'pong'. Note the use of 'smtProductiveFunction':
-- since @ping@ and @pong@ are corecursive (no base case, always producing output), we
-- declare them productive instead of terminating.
ping :: SInteger -> SList Integer
ping = smtProductiveFunction "ping"
     $ \n -> n .: pong (n + 1)

-- | @pong n@ emits @n@ and hands off to 'ping'. See 'ping' for why we use 'smtProductiveFunction'.
pong :: SInteger -> SList Integer
pong = smtProductiveFunction "pong"
     $ \n -> n .: ping (n + 1)

-- * Helper lemmas

-- | @ping@ produces unboundedly long lists.
--
-- >>> runTP pingLen
-- Inductive lemma: pingLen
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- Functions proven productive: ping, pong
-- [Proven] pingLen :: Ɐm ∷ Integer → Ɐn ∷ Integer → Bool
pingLen :: TP (Proof (Forall "m" Integer -> Forall "n" Integer -> SBool))
pingLen = inductWith cvc5 "pingLen"
                     (\(Forall @"m" (m :: SInteger)) (Forall @"n" n) -> length (ping n) .>= m) $
                     \ih m n -> []
                             |- length (ping n) .>= m + 1
                             =: length (n .: pong (n + 1)) .>= m + 1
                             ?? ih `at` Inst @"n" (n + 2)
                             =: sTrue
                             =: qed

-- | @pong@ produces unboundedly long lists.
--
-- >>> runTP pongLen
-- Inductive lemma: pongLen
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- Functions proven productive: ping, pong
-- [Proven] pongLen :: Ɐm ∷ Integer → Ɐn ∷ Integer → Bool
pongLen :: TP (Proof (Forall "m" Integer -> Forall "n" Integer -> SBool))
pongLen = inductWith cvc5 "pongLen"
                     (\(Forall @"m" (m :: SInteger)) (Forall @"n" n) -> length (pong n) .>= m) $
                     \ih m n -> []
                             |- length (pong n) .>= m + 1
                             =: length (n .: ping (n + 1)) .>= m + 1
                             ?? ih `at` Inst @"n" (n + 2)
                             =: sTrue
                             =: qed

-- | Indexing past a cons: @(x .: y) !! k == y !! (k - 1)@ when @k > 0@ and in bounds.
--
-- >>> runTP consIndex
-- Lemma: consIndex                        Q.E.D.
-- [Proven] consIndex :: Ɐx ∷ Integer → Ɐy ∷ [Integer] → Ɐk ∷ Integer → Bool
consIndex :: TP (Proof (Forall "x" Integer -> Forall "y" [Integer] -> Forall "k" Integer -> SBool))
consIndex = lemma "consIndex"
                  (\(Forall @"x" (x :: SInteger)) (Forall @"y" y) (Forall @"k" k) ->
                        k .> 0 .&& k .<= length y .=> (x .: y) !! k .== y !! (k - 1))
                  []

-- * Correctness

-- | Proving @ping n@ and @pong n@ produce the same elements. We prove that the @k@-th
-- elements are the same, by induction on @k@.
--
-- >>> runTP pingEqPong
-- Lemma: pingLen                          Q.E.D.
-- Lemma: pongLen                          Q.E.D.
-- Lemma: consIndex                        Q.E.D.
-- Inductive lemma: pingEqPong
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- Functions proven productive: ping, pong
-- [Proven] pingEqPong :: Ɐk ∷ Integer → Ɐn ∷ Integer → Bool
pingEqPong :: TP (Proof (Forall "k" Integer -> Forall "n" Integer -> SBool))
pingEqPong = do
   piLen <- recall pingLen
   poLen <- recall pongLen
   ci    <- recall consIndex

   inductWith cvc5 "pingEqPong"
          (\(Forall @"k" k) (Forall @"n" n) -> k .>= 0 .=> ping n !! k .== pong n !! k) $
          \ih k n -> [k .>= 0]
                  |- ping n !! (k + 1)
                  =: (n .: pong (n + 1)) !! (k + 1)
                  ?? ci `at` (Inst @"x" n, Inst @"y" (pong (n + 1)), Inst @"k" (k + 1))
                  ?? poLen
                  =: pong (n + 1) !! k
                  ?? ih `at` Inst @"n" (n + 1)
                  =: ping (n + 1) !! k
                  ?? ci `at` (Inst @"x" n, Inst @"y" (ping (n + 1)), Inst @"k" (k + 1))
                  ?? piLen
                  =: (n .: ping (n + 1)) !! (k + 1)
                  =: pong n !! (k + 1)
                  =: qed

-- | The @k@-th element of @ping n@ is @n + k@.
--
-- >>> runTP pingElem
-- Lemma: pingEqPong                       Q.E.D.
-- Lemma: consIndex                        Q.E.D. [Cached]
-- Lemma: pongLen                          Q.E.D. [Cached]
-- Inductive lemma: pingElem
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- Functions proven productive: ping, pong
-- [Proven] pingElem :: Ɐk ∷ Integer → Ɐn ∷ Integer → Bool
pingElem :: TP (Proof (Forall "k" Integer -> Forall "n" Integer -> SBool))
pingElem = do
   eq    <- recall pingEqPong
   ci    <- recall consIndex
   poLen <- recall pongLen

   inductWith cvc5 "pingElem"
          (\(Forall @"k" k) (Forall @"n" n) -> k .>= 0 .=> ping n !! k .== n + k) $
          \ih k n -> [k .>= 0]
                  |- ping n !! (k + 1)
                  =: (n .: pong (n + 1)) !! (k + 1)
                  ?? ci `at` (Inst @"x" n, Inst @"y" (pong (n + 1)), Inst @"k" (k + 1))
                  ?? poLen
                  =: pong (n + 1) !! k
                  ?? eq `at` (Inst @"k" k, Inst @"n" (n + 1))
                  =: ping (n + 1) !! k
                  ?? ih `at` Inst @"n" (n + 1)
                  =: (n + 1) + k
                  =: n + (k + 1)
                  =: qed
