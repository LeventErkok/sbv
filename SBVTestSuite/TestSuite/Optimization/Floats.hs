-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Optimization.Floats
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for optimization routines, floats
-----------------------------------------------------------------------------

module TestSuite.Optimization.Floats (tests) where

import Control.Monad (when)

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Optimization.Floats"
    [ goldenVsStringShow "optFloat1a" $ optimizeWith z3{printBase=16} Lexicographic (floatMinMax  (minimize "min-x") True)
    , goldenVsStringShow "optFloat1b" $ optimizeWith z3{printBase=16} Lexicographic (floatMinMax  (minimize "min-x") False)
    , goldenVsStringShow "optFloat1c" $ optimizeWith z3{printBase=16} Lexicographic (floatMinMax  (maximize "max-x") True)
    , goldenVsStringShow "optFloat1d" $ optimizeWith z3{printBase=16} Lexicographic (floatMinMax  (maximize "max-y") False)
    , goldenVsStringShow "optFloat2a" $ optimizeWith z3{printBase=16} Lexicographic (doubleMinMax (minimize "min-x") True)
    , goldenVsStringShow "optFloat2b" $ optimizeWith z3{printBase=16} Lexicographic (doubleMinMax (minimize "min-x") False)
    , goldenVsStringShow "optFloat2c" $ optimizeWith z3{printBase=16} Lexicographic (doubleMinMax (maximize "max-x") True)
    , goldenVsStringShow "optFloat2d" $ optimizeWith z3{printBase=16} Lexicographic (doubleMinMax (maximize "max-y") False)
    , goldenVsStringShow "optFloat3"  $ optimizeWith z3{printBase=16} Lexicographic q
    , goldenVsStringShow "optFloat4"  $ optimizeWith z3{printBase=16} Lexicographic r
    ]

floatMinMax :: (SFloat -> Symbolic ()) -> Bool -> Goal
floatMinMax opt reqPoint = do x <- sFloat "x"

                              when reqPoint $ constrain $ fpIsPoint x

                              opt x

doubleMinMax :: (SDouble -> Symbolic ()) -> Bool -> Goal
doubleMinMax opt reqPoint = do x <- sDouble "x"

                               when reqPoint $ constrain $ fpIsPoint x

                               opt x

q :: Goal
q = do x <- sFloat "x"
       y <- sFloat "y"

       constrain $ fpIsPoint x
       constrain $ fpIsPoint y
       constrain $ x .== y
       constrain $ x .> 0
       constrain $ fpIsPoint $ x+y

       maximize "metric-max-x+y" $ observe "max-x+y" (x+y)

r :: Goal
r = do x <- sFloat "x"
       y <- sFloat "y"

       constrain $ fpIsPoint x
       constrain $ fpIsPoint y
       constrain $ x .== y
       constrain $ x .> 0
       constrain $ fpIsPoint $ x+y

       minimize "metric-min-x+y" $ observe "min-x+y" (x+y)

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
