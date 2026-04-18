-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.NatStream
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrating productive (corecursive) functions. A productive function
-- is one where every recursive call is guarded by a data constructor, so
-- the function always makes progress by producing output. Unlike terminating
-- functions, productive functions need not have a base case and may produce
-- infinite output.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.NatStream where

import Prelude hiding (head, length, (!!))

import Data.SBV
import Data.SBV.List
import Data.SBV.TP

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV.TP
#endif

-- * Definitions

-- | The infinite stream of integers starting from @n@: @[n, n+1, n+2, ...]@.
-- There is no base case; every recursive call is guarded by the list
-- constructor @.:@, making this a productive (corecursive) definition.
nats :: SInteger -> SList Integer
nats = smtProductiveFunction "nats"
     $ \n -> n .: nats (n + 1)

-- * Correctness

-- | Prove that @nats n@ always starts with @n@.
--
-- NB. As of Mar 2026, z3 can't handle this but cvc5 can.
--
-- >>> runTP natsHead
-- Lemma: natsHead    Q.E.D.
-- Functions proven productive: nats
-- [Proven] natsHead :: Ɐn ∷ Integer → Bool
natsHead :: TP (Proof (Forall "n" Integer -> SBool))
natsHead = lemmaWith cvc5 "natsHead"
                 (\(Forall @"n" n) -> head (nats n) .== n)
                 []

-- | Prove by induction that @nats n@ has at least @m@ elements, for any @m@.
-- This captures the idea that @nats@ produces an unboundedly long list.
--
-- NB. As of Mar 2026, z3 can't handle this but cvc5 can.
--
-- >>> runTP natsLen
-- Inductive lemma: natsLen
--   Step: Base                Q.E.D.
--   Step: 1                   Q.E.D.
--   Step: 2                   Q.E.D.
--   Result:                   Q.E.D.
-- Functions proven productive: nats
-- [Proven] natsLen :: Ɐm ∷ Integer → Ɐn ∷ Integer → Bool
natsLen :: TP (Proof (Forall "m" Integer -> Forall "n" Integer -> SBool))
natsLen =
   inductWith cvc5 "natsLen"
          (\(Forall @"m" m) (Forall @"n" n) -> length (nats n) .>= m) $
          \ih m n -> []
                  |- length (nats n) .>= m + 1
                  =: length (n .: nats (n + 1)) .>= m + 1
                  ?? ih `at` Inst @"n" (n + 1)
                  =: sTrue
                  =: qed

-- | Prove by induction that the @k@-th element of @nats n@ is @n + k@.
--
-- NB. As of Mar 2026, z3 can't handle this but cvc5 can.
--
-- >>> runTP natsElem
-- Lemma: natsLen               Q.E.D.
-- Lemma: elemOne               Q.E.D.
-- Inductive lemma: natsElem
--   Step: Base                 Q.E.D.
--   Step: 1                    Q.E.D.
--   Step: 2                    Q.E.D.
--   Step: 3                    Q.E.D.
--   Step: 4                    Q.E.D.
--   Result:                    Q.E.D.
-- Functions proven productive: nats
-- [Proven] natsElem :: Ɐk ∷ Integer → Ɐn ∷ Integer → Bool
natsElem :: TP (Proof (Forall "k" Integer -> Forall "n" Integer -> SBool))
natsElem = do
   nLen <- recall natsLen

   elemOne <- lemma "elemOne"
                    (\(Forall @"x" (x :: SInteger)) (Forall @"y" y) (Forall @"k" k) ->
                          k .> 0 .&& k .<= length y .=> (x .: y) !! k .== y !! (k - 1))
                    []

   inductWith cvc5 "natsElem"
          (\(Forall @"k" k) (Forall @"n" n) -> k .>= 0 .=> nats n !! k .== n + k) $
          \ih k n -> [k .>= 0]
                  |- nats n !! (k + 1)
                  =: (n .: nats (n + 1)) !! (k + 1)
                  ?? elemOne
                  ?? nLen
                  =: nats (n + 1) !! k
                  ?? ih `at` Inst @"n" (n + 1)
                  =: (n + 1) + k
                  =: n + (k + 1)
                  =: qed
