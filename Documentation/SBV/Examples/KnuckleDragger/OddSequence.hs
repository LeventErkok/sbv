-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.OddSequence
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Example of strong induction principle, proving the following statement:
-- The sequence of numbers defined by @S_0 = 1@, @S_1 = 3@, and @S_k = S_{k-2} + 2 S_{k-1}@
-- is always odd. The proof also demonstrates proof-by-contradiction, as we start
-- with the negation of the goal and derive falsehood.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.OddSequence where

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

-- Prove that the sequence @1@, @3@, @S_{k-2} + 2 S_{k-1}@ is always odd.
--
-- We have:
--
-- >>> oddSequence
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
oddSequence :: IO Proof
oddSequence = runKD $ do
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
