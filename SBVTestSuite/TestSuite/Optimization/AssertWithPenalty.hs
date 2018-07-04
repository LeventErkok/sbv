-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Optimization.AssertWithPenalty
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for optimization routines, soft assertions
-----------------------------------------------------------------------------

module TestSuite.Optimization.AssertWithPenalty(tests) where

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Optimization.AssertWithPenalty"
    [ goldenVsStringShow "assertWithPenalty1" (optimize Lexicographic assertWithPenalty1)
    , goldenVsStringShow "assertWithPenalty2" (optimize Lexicographic assertWithPenalty2)
    ]

assertWithPenalty1 :: Goal
assertWithPenalty1 = do
                 x <- sInteger "x"
                 y <- sInteger "y"

                 let a1 = x .> 0
                     a2 = x .< y
                     a3 = x+y .<= 0

                 constrain $ a1 .== a3
                 constrain $ a3 ||| a2

                 assertWithPenalty "as1" a3        (Penalty  3 Nothing)
                 assertWithPenalty "as2" (bnot a3) (Penalty  5 Nothing)
                 assertWithPenalty "as3" (bnot a1) (Penalty 10 Nothing)
                 assertWithPenalty "as4" (bnot a2) (Penalty  3 Nothing)

assertWithPenalty2 :: Goal
assertWithPenalty2 = do
                 a1 <- sBool "a1"
                 a2 <- sBool "a2"
                 a3 <- sBool "a3"

                 assertWithPenalty "as_a1" a1                    (Penalty  0.1 Nothing)
                 assertWithPenalty "as_a2" a2                    (Penalty  1.0 Nothing)
                 assertWithPenalty "as_a3" a3                    (Penalty  1   Nothing)
                 assertWithPenalty "as_a4" (bnot a1 ||| bnot a2) (Penalty 3.2 Nothing)
