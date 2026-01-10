-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.TacticStyle
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Examples demonstrating the tactic-based proof interface.
-- Compare these to the calculational style in other TP examples.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.TacticStyle where

import Prelude hiding ((>>))

import Data.SBV
import Data.SBV.TP.Tactics

-- * Basic examples

-- | Prove that true is provable, using tactics
--
-- >>> trueByTactics
-- [Proven] true_tactics :: Bool
trueByTactics :: IO (Proof SBool)
trueByTactics = runTP $ theorem "true_tactics" sTrue auto

-- | Prove a simple implication using tactics
--
-- This proof shows the basic structure:
--   1. We have some assumption
--   2. We prove the goal using auto
simpleTacticProof :: IO (Proof (Forall "x" Integer -> SBool))
simpleTacticProof = runTP $
  theorem "simple_tactic"
          (\(Forall x) -> x .> 0 .=> x + 1 .> 1)
          auto

-- * Case splitting with tactics

-- | Prove that 2n^2 + n + 1 is not divisible by 3, using tactics
--
-- Compare this to Documentation.SBV.Examples.TP.CaseSplit which uses
-- the calculational style. The tactic version makes the case analysis
-- more explicit.
--
-- Note: splitOn automatically adds an exhaustiveness goal to ensure
-- the cases cover all possibilities. In this case, it proves that
-- (n mod 3 == 0) ∨ (n mod 3 == 1) ∨ (n mod 3 == 2) is always true.
notDiv3Tactics :: IO (Proof (Forall "n" Integer -> SBool))
notDiv3Tactics = runTP $ do

  theorem "notDiv3_tactics"
          (\(Forall n) -> s n `sEMod` 3 ./= 0) $

    -- Split into three cases based on n mod 3
    splitOn [ ("n_mod_0", nVal `sEMod` 3 .== 0)
            , ("n_mod_1", nVal `sEMod` 3 .== 1)
            , ("n_mod_2", nVal `sEMod` 3 .== 2)
            ] >>

    -- In each case, the SMT solver can figure it out
    allGoals auto

  where
    s m = 2 * m * m + m + 1
    nVal :: SInteger
    nVal = uninterpret "n"

-- * Using helper lemmas with tactics

-- | First prove a helper lemma
helperLemma :: TP (Proof (Forall "x" Integer -> SBool))
helperLemma = theorem "helper" (\(Forall x) -> x + 1 .> x) auto

-- | Then use it in another proof
usingHelpers :: IO (Proof (Forall "x" Integer -> SBool))
usingHelpers = runTP $ do
  helper <- helperLemma

  theorem "main_proof"
          (\(Forall x) -> x .>= 0 .=> x + 1 .> 0) $
    using [helper] >> auto

-- * Structured proofs with intermediate steps

-- | A proof showing basic usage
structuredProof :: IO (Proof (Forall "x" Integer -> SBool))
structuredProof = runTP $
  theorem "structured"
          (\(Forall x) -> x .> 10 .=> x * x .> 100)
          auto

-- * Case analysis with different tactics per case

-- | Prove something by cases, with different tactics for each case
caseByCase :: IO (Proof (Forall "n" Integer -> SBool))
caseByCase = runTP $
  theorem "case_by_case"
          (\(Forall n) -> n * n .>= 0) $

    considerCases
      [ ("n_positive", nVal .>= 0, auto)
      , ("n_negative", nVal .<  0, auto)
      ]

  where
    nVal :: SInteger
    nVal = uninterpret "n"

-- * Goal manipulation

-- | Example showing goal manipulation tactics
goalManipulation :: IO (Proof (Forall "x" Integer -> Forall "y" Integer -> SBool))
goalManipulation = runTP $
  theorem "goal_manip"
          (\(Forall x) (Forall y) -> x + y .== y + x) $

    -- We could defer this goal and come back to it
    -- defer >>

    -- Or just prove it directly
    auto

-- * Inspecting proof state

-- | A proof that shows how to inspect the state mid-proof
inspectingState :: TP (Proof (Forall "x" Integer -> SBool))
inspectingState = do

  theorem "inspecting"
          (\(Forall x) -> x .> 0 .=> x .>= 1) $

    -- Show what goals we have
    showGoals >>

    -- Try to prove it
    auto

-- * Combining tactics

-- | Use tactic combinators to build complex proof strategies
combinedTactics :: IO (Proof (Forall "x" Integer -> SBool))
combinedTactics = runTP $
  theorem "combined"
          (\(Forall x) -> x * 2 .== 2 * x) $

    -- Try multiple strategies
    tryAll [ auto
           , using [] >> auto
           ]

-- * Interactive-style proof

-- | A more interactive-looking proof (even though it's not actually interactive)
interactiveStyle :: IO (Proof (Forall "x" Integer -> Forall "y" Integer -> SBool))
interactiveStyle = runTP $ do

  -- First prove a helper lemma
  addComm <- theorem "add_commutative"
                     (\(Forall @"a" (x :: SInteger)) (Forall @"b" y) -> x + y .== y + x)
                     auto

  -- Now prove the main theorem using the lemma
  theorem "main_theorem"
          (\(Forall @"x" (x :: SInteger)) (Forall @"y" y) ->
            (x + y) + (y + x) .== 2 * (x + y)) $
    using [addComm] >>
    auto

-- * Backwards reasoning

-- | Example showing backwards reasoning
backwardsReasoning :: IO (Proof (Forall "x" Integer -> SBool))
backwardsReasoning = runTP $
  theorem "backwards"
          (\(Forall x) -> x .> 10 .=> x .> 5)
          auto

-- * Comparison with calculational style

-- | The same proof in calculational style (for comparison)
calcStyle :: TP (Proof (Forall "x" Integer -> SBool))
calcStyle = calc "calc_version"
                 (\(Forall (x :: SInteger)) -> x + 1 .> x) $
                 \x -> [] |- x + 1
                        =: x + 1
                        =: qed

-- | The same proof in tactic style
tacticStyle :: TP (Proof (Forall "x" Integer -> SBool))
tacticStyle = theorem "tactic_version"
                      (\(Forall (x :: SInteger)) -> x + 1 .> x)
                      auto

{-
Key differences between styles:

Calculational style:
  + Natural for equational reasoning
  + Shows step-by-step derivations explicitly
  + Good for mathematical calculations
  - Can get deeply nested with case splits
  - Less composable

Tactic style:
  + More composable (tactics are values)
  + Better for complex case analysis
  + Goal state is explicit
  + Familiar to Coq/Lean users
  - Doesn't show intermediate calculation steps
  - Requires understanding of tactic combinators
-}
