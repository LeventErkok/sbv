-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Optimization.ExtensionField
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for optimization routines, extension field
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Optimization.ExtensionField(tests) where

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Optimization.ExtensionField"
    [ goldenVsStringShow "optExtField1" (optimize Lexicographic optExtField1)
    , goldenVsStringShow "optExtField2" (optimize Lexicographic optExtField2)
    , goldenVsStringShow "optExtField3" (optimize Lexicographic optExtField3)
    ]

optExtField1 :: ConstraintSet
optExtField1 = do x <- sInteger "x"
                  y <- sInteger "y"

                  constrain $ x .< 4
                  constrain $ y - x .> 1

                  maximize "x_plus_y" $ x+y

optExtField2 :: ConstraintSet
optExtField2 = do x <- sInteger "x"
                  y <- sInteger "y"

                  constrain $ x .< 4
                  constrain $ y - x .< 1
                  constrain $ y .< 1

                  minimize "x_plus_y" $ x+y

optExtField3 :: ConstraintSet
optExtField3 = do x <- sReal "x"
                  y <- sReal "y"

                  constrain $ x .<= 4
                  constrain $ y .<= 5

                  maximize "x_plus_y" $ x + y

{- HLint ignore module "Reduce duplication" -}
