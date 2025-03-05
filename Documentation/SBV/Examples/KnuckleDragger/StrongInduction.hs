-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.StrongInduction
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Examples of strong induction on integers.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.StrongInduction where

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

-- | Prove that the sequence @1@, @3@, @S_{k-2} + 2 S_{k-1}@ is always odd.
--
-- We have:
--
-- >>> oddSequence1
-- Inductive lemma (strong): oddSequence
--   Base: oddSequence.Base                Q.E.D.
--   Asms: 1                               Q.E.D.
--   Step 1: Case split one way:
--     Case [1 of 1]: n[1]                 Q.E.D.
--     Completeness:                       Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: oddSequence.Step                Q.E.D.
-- [Proven] oddSequence
oddSequence1 :: IO Proof
oddSequence1 = runKD $ do
  let s :: SInteger -> SInteger
      s = smtFunction "seq" $ \n -> ite (n .<= 0) 1
                                  $ ite (n .== 1) 3
                                  $ s (n-2) + 2 * s (n-1)

  -- z3 can't handle this, but CVC5 is proves it just fine.
  -- Note also that we do a "proof-by-contradiction," by deriving that
  -- the negation of the goal leads to falsehood.
  sInductWith cvc5 "oddSequence"
          (\(Forall @"n" n) -> n .>= 0 .=> sNot (2 `sDivides` s n)) $
          \ih n -> [n .>= 0] |- 2 `sDivides` s (n+1)
                             ?? [cases "n" [n .< 2],  hyp (n .>= 0)]
                             =: 2 `sDivides` (s (n-1) + 2 * s n)
                             =: 2 `sDivides` (s (n-1))
                             ?? ih `at` Inst @"n" (n - 1)
                             =: sFalse
                             =: qed

-- | Prove that the sequence @1@, @3@, @2 S_{k-1} - S_{k-2}@ generates sequence of odd numbers.
--
-- We have:
--
-- >>> oddSequence2
-- Inductive lemma (strong): oddSequence
--   Base: oddSequence.Base                Q.E.D.
--   Asms: 1                               Q.E.D.
--   Step 1: Case split one way:
--     Case [1 of 1]: n[1]                 Q.E.D.
--     Completeness:                       Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Step: 7                               Q.E.D.
--   Step: oddSequence.Step                Q.E.D.
-- [Proven] oddSequence
oddSequence2 :: IO Proof
oddSequence2 = runKD $ do
  let s :: SInteger -> SInteger
      s = smtFunction "seq" $ \n -> ite (n .<= 0) 1
                                  $ ite (n .== 1) 3
                                  $ 2 * s (n-1) - s (n-2)

  sInduct "oddSequence"
          (\(Forall @"n" n) -> n .>= 0 .=> s n .== 2 * n + 1) $
          \ih n -> [n .>= 0] |- s (n+1)
                             ?? [cases "n" [n+1 .< 2],  hyp (n .>= 0)]
                             =: let focus v = ite (n+1 .<= 0) 1 (ite (n + 1 .== 1) 3 v)
                             in focus (2 * s n - s (n-1))
                             ?? ih `at` Inst @"n" n
                             =: focus (2 * (2 * n + 1) - s (n - 1))
                             ?? ih `at` Inst @"n" (n-1)
                             =: focus (2 * (2 * n + 1) - (2 * (n - 1) + 1))
                             =: focus (4 * n + 2 - (2 * n - 1))
                             =: focus (4 * n + 2 - 2 * n + 1)
                             =: focus (2 * n + 2 + 1)
                             =: focus (2 * (n + 1) + 1)
                             =: qed
