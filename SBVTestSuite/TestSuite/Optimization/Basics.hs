-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Optimization.Basics
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for optimization routines
-----------------------------------------------------------------------------

module TestSuite.Optimization.Basics(tests) where

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Optimization.Basics"
    [ goldenVsStringShow "optBasics1" (optimize Lexicographic optBasics1)
    , goldenVsStringShow "optBasics2" (optimize Lexicographic optBasics2)
    ]

optBasics1 :: Goal
optBasics1 = do x <- sInteger "x"
                y <- sInteger "y"

                constrain $ x .< 2
                constrain $ y - x .< 1

                maximize "x_plus_y" $ x+y

optBasics2 :: Goal
optBasics2 = do x <- sInteger "x"
                y <- sInteger "y"

                constrain $ x .< 4
                constrain $ y - x .< 1
                constrain $ y .> 1

                minimize "x_plus_y" $ x+y
