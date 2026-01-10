-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.GoalManipulation
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Examples demonstrating goal manipulation tactics: defer, focus, swap, rotate.
-- These tactics are useful for managing proof complexity by controlling
-- the order in which goals are proven.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.GoalManipulation where

import Prelude hiding ((>>))

import Data.SBV hiding (rotate)
import Data.SBV.TP.Tactics

-- * Example 1: Using defer to postpone harder goals

-- | Prove properties about quadratic functions
--
-- This example shows using 'defer' to postpone a harder goal.
-- We have three properties to prove, and we defer the hardest one.
--
-- >>> quadraticProperties
-- [Proven] quadratic_props :: Ɐx ∷ Integer → Bool
quadraticProperties :: IO (Proof (Forall "x" Integer -> SBool))
quadraticProperties = runTP $ do
  theorem "quadratic_props"
          (\(Forall @"x" (x :: SInteger)) ->
            -- Three properties combined
            let prop1 = x * x .>= 0              -- Squares are non-negative (easy)
                prop2 = x + x .== 2 * x          -- Distributivity (easy)
                prop3 = (x + 1) * (x - 1) .== x * x - 1  -- Difference of squares (harder)
            in prop1 .&& prop2 .&& prop3) $

    -- Show the initial goals
    showGoals >>

    -- Split the conjunction into separate goals
    -- This creates 3 goals, all at once
    splitOn [ ("squares_nonneg", xVal * xVal .>= 0)
            , ("distributive", xVal + xVal .== 2 * xVal)
            , ("diff_squares", (xVal + 1) * (xVal - 1) .== xVal * xVal - 1)
            ] >>

    -- Defer the hardest goal (difference of squares) to the end
    focus 3 defer >>

    showGoals >>

    -- Now prove the easier goals first
    auto >>  -- proves squares_nonneg
    auto >>  -- proves distributive
    auto     -- proves diff_squares (and exhaustiveness)

  where
    xVal :: SInteger
    xVal = uninterpret "x"


-- * Example 2: Using swap to reorder goals

-- | Prove properties about absolute value
--
-- Shows using 'swap' to reorder goals when you want to tackle them
-- in a different order than they were generated.
--
-- >>> absoluteValueProps
-- [Proven] abs_props :: Ɐx ∷ Integer → Bool
absoluteValueProps :: IO (Proof (Forall "x" Integer -> SBool))
absoluteValueProps = runTP $ do
  theorem "abs_props"
          (\(Forall @"x" (x :: SInteger)) ->
            let absX = ite (x .>= 0) x (-x)
                prop1 = absX .>= 0                    -- abs is non-negative
                prop2 = absX * absX .== x * x         -- abs(x)^2 = x^2
            in prop1 .&& prop2) $

    -- Split into the two properties
    considerCases
      [ ("positive", xVal .>= 0,
          -- For positive x, both properties are straightforward
          auto)
      , ("negative", xVal .< 0,
          -- For negative x, let's swap the goals
          -- We'll prove abs(x)^2 = x^2 before abs(x) >= 0
          showGoals >>
          swap >>
          showGoals >>
          auto >> auto)
      ]

  where
    xVal :: SInteger
    xVal = uninterpret "x"


-- * Example 3: Using focus to work on specific goals

-- | Prove multiple divisibility properties
--
-- Demonstrates 'focus' to selectively work on specific goals by index.
--
-- >>> divisibilityProps
-- [Proven] divisibility_props :: Ɐn ∷ Integer → Bool
divisibilityProps :: IO (Proof (Forall "n" Integer -> SBool))
divisibilityProps = runTP $ do
  theorem "divisibility_props"
          (\(Forall @"n" (n :: SInteger)) ->
            -- Multiple divisibility properties
            let even_plus_even =
                  (n `sEMod` 2 .== 0) .=> ((n + 2) `sEMod` 2 .== 0)
                times_four =
                  (n `sEMod` 4 .== 0) .=> (n `sEMod` 2 .== 0)
                times_six =
                  (n `sEMod` 6 .== 0) .=> ((n `sEMod` 2 .== 0) .&& (n `sEMod` 3 .== 0))
            in even_plus_even .&& times_four .&& times_six) $

    showGoals >>

    -- Create three separate goals
    splitOn [ ("even_plus_even",
               (nVal `sEMod` 2 .== 0) .=> ((nVal + 2) `sEMod` 2 .== 0))
            , ("times_four",
               (nVal `sEMod` 4 .== 0) .=> (nVal `sEMod` 2 .== 0))
            , ("times_six",
               (nVal `sEMod` 6 .== 0) .=> ((nVal `sEMod` 2 .== 0) .&& (nVal `sEMod` 3 .== 0)))
            ] >>

    showGoals >>

    -- Focus on goal 2 (times_four) first - it's the easiest
    focus 2 auto >>

    -- Now focus on goal 1 (even_plus_even)
    focus 1 auto >>

    -- Finally prove the remaining goal (times_six)
    auto >>

    -- And the exhaustiveness goal
    auto

  where
    nVal :: SInteger
    nVal = uninterpret "n"


-- * Example 4: Using rotate to cycle through goals

-- | Prove properties about modular arithmetic
--
-- Shows 'rotate' to cycle through goals in a round-robin fashion.
--
-- >>> modularArithmeticProps
-- [Proven] mod_props :: Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
modularArithmeticProps :: IO (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
modularArithmeticProps = runTP $ do
  theorem "mod_props"
          (\(Forall @"a" (a :: SInteger)) (Forall @"b" b) ->
            let prop1 = (a + b) `sEMod` 2 .== ((a `sEMod` 2) + (b `sEMod` 2)) `sEMod` 2
                prop2 = (a * b) `sEMod` 2 .== ((a `sEMod` 2) * (b `sEMod` 2)) `sEMod` 2
                prop3 = a `sEMod` 1 .== 0
            in prop1 .&& prop2 .&& prop3) $

    -- Split into three goals
    splitOn [ ("mod_addition", (aVal + bVal) `sEMod` 2 .== ((aVal `sEMod` 2) + (bVal `sEMod` 2)) `sEMod` 2)
            , ("mod_multiplication", (aVal * bVal) `sEMod` 2 .== ((aVal `sEMod` 2) * (bVal `sEMod` 2)) `sEMod` 2)
            , ("mod_one", aVal `sEMod` 1 .== 0)
            ] >>

    showGoals >>

    -- Rotate to bring the easiest goal (mod_one) to the front
    rotate 2 >>

    showGoals >>

    -- Now solve in the new order
    allGoals auto

  where
    aVal, bVal :: SInteger
    aVal = uninterpret "a"
    bVal = uninterpret "b"


-- * Example 5: Complex orchestration with multiple tactics

-- | A complex proof showing orchestration of multiple goal manipulation tactics
--
-- This example demonstrates a realistic scenario where you need to
-- carefully manage multiple subgoals.
--
-- >>> complexOrchestration
-- [Proven] complex_proof :: Ɐx ∷ Integer → Ɐy ∷ Integer → Bool
complexOrchestration :: IO (Proof (Forall "x" Integer -> Forall "y" Integer -> SBool))
complexOrchestration = runTP $ do
  theorem "complex_proof"
          (\(Forall @"x" (x :: SInteger)) (Forall @"y" y) ->
            -- A collection of properties about x and y
            let commutative = x + y .== y + x
                associative = (x + y) + 1 .== x + (y + 1)
                distributive = 2 * (x + y) .== 2 * x + 2 * y
                square_sum = (x + y) * (x + y) .>= 0
            in commutative .&& associative .&& distributive .&& square_sum) $

    -- Split into four goals
    splitOn [ ("comm", xVal + yVal .== yVal + xVal)
            , ("assoc", (xVal + yVal) + 1 .== xVal + (yVal + 1))
            , ("dist", 2 * (xVal + yVal) .== 2 * xVal + 2 * yVal)
            , ("square", (xVal + yVal) * (xVal + yVal) .>= 0)
            ] >>

    -- Initial state
    showGoals >>

    -- Strategy:
    -- 1. Defer the "hard" goal (dist) to the end
    -- 2. Swap to put square first (it's easiest)
    -- 3. Solve in the new order

    focus 3 defer >>      -- defer distributive
    rotate 2 >>           -- bring square to front

    showGoals >>

    auto >>  -- square
    auto >>  -- comm
    auto >>  -- assoc
    auto >>  -- dist
    auto     -- exhaustiveness

  where
    xVal, yVal :: SInteger
    xVal = uninterpret "x"
    yVal = uninterpret "y"


-- * Example 6: Interactive-style proof with defer

-- | Build a proof incrementally, deferring unknowns
--
-- This shows a more "interactive" style where we defer goals we're
-- not ready to prove yet, prove what we can, then come back to them.
--
-- >>> incrementalProof
-- [Proven] incremental :: Ɐx ∷ Integer → Bool
incrementalProof :: IO (Proof (Forall "x" Integer -> SBool))
incrementalProof = runTP $ do
  theorem "incremental"
          (\(Forall @"x" (x :: SInteger)) ->
            -- Multiple properties, some obvious, some less so
            x + 0 .== x .&&                    -- identity (obvious)
            x * 1 .== x .&&                    -- identity (obvious)
            x - x .== 0 .&&                    -- inverse (obvious)
            x + x .== 2 * x) $                 -- distributive (less obvious)

    -- Split into goals
    splitOn [ ("add_zero", xVal + 0 .== xVal)
            , ("mult_one", xVal * 1 .== xVal)
            , ("sub_self", xVal - xVal .== 0)
            , ("double", xVal + xVal .== 2 * xVal)
            ] >>

    -- "Hmm, let's defer the one we're less sure about"
    focus 4 defer >>

    -- Prove the obvious ones
    auto >>  -- add_zero
    auto >>  -- mult_one
    auto >>  -- sub_self

    -- Now we're ready to tackle the deferred one
    auto >>  -- double
    auto     -- exhaustiveness

  where
    xVal :: SInteger
    xVal = uninterpret "x"

{-
Summary of Goal Manipulation Tactics:

* defer:
  - Moves the current goal to the end of the goal list
  - Useful for postponing harder goals
  - Example: defer

* focus n tac:
  - Applies tactic 'tac' to the nth goal (1-indexed)
  - Useful for working on specific goals out of order
  - Example: focus 3 auto

* swap:
  - Swaps the first two goals
  - Useful for reordering when you want to tackle goals in different order
  - Example: swap

* rotate n:
  - Rotates the goal list by n positions
  - Useful for bringing a specific goal to the front
  - Example: rotate 2

These tactics help manage proof complexity by giving you control over
the order in which goals are proven, making it easier to:
- Prove easy goals first to build confidence
- Defer difficult goals until you have more context
- Group related goals together
- Create a natural flow in the proof narrative
-}
