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

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Optimization.Floats (tests) where

import Control.Monad (when)

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Optimization.Floats"
    [ goldenVsStringShow "optFloat1a" $ optimizeWith z3{crackNum=True} Lexicographic (floatMinMax  (minimize "min-x") True)
    , goldenVsStringShow "optFloat1b" $ optimizeWith z3{crackNum=True} Lexicographic (floatMinMax  (minimize "min-x") False)
    , goldenVsStringShow "optFloat1c" $ optimizeWith z3{crackNum=True} Lexicographic (floatMinMax  (maximize "max-x") True)
    , goldenVsStringShow "optFloat1d" $ optimizeWith z3{crackNum=True} Lexicographic (floatMinMax  (maximize "max-y") False)
    , goldenVsStringShow "optFloat2a" $ optimizeWith z3{crackNum=True} Lexicographic (doubleMinMax (minimize "min-x") True)
    , goldenVsStringShow "optFloat2b" $ optimizeWith z3{crackNum=True} Lexicographic (doubleMinMax (minimize "min-x") False)
    , goldenVsStringShow "optFloat2c" $ optimizeWith z3{crackNum=True} Lexicographic (doubleMinMax (maximize "max-x") True)
    , goldenVsStringShow "optFloat2d" $ optimizeWith z3{crackNum=True} Lexicographic (doubleMinMax (maximize "max-y") False)
    , goldenVsStringShow "optFloat3"  $ optimizeWith z3{crackNum=True} Lexicographic q
    , goldenVsStringShow "optFloat4"  $ optimizeWith z3{crackNum=True} Lexicographic r
    ]

floatMinMax :: (SFloat -> Symbolic ()) -> Bool -> ConstraintSet
floatMinMax opt reqPoint = do x <- sFloat "x"

                              when reqPoint $ constrain $ fpIsPoint x

                              opt x

doubleMinMax :: (SDouble -> Symbolic ()) -> Bool -> ConstraintSet
doubleMinMax opt reqPoint = do x <- sDouble "x"

                               when reqPoint $ constrain $ fpIsPoint x

                               opt x

q :: ConstraintSet
q = do x <- sFloat "x"
       y <- sFloat "y"

       constrain $ fpIsPoint x
       constrain $ fpIsPoint y
       constrain $ x .== y
       constrain $ x .> 0
       constrain $ fpIsPoint $ x+y

       maximize "metric-max-x+y" $ observe "max-x+y" (x+y)

r :: ConstraintSet
r = do x <- sFloat "x"
       y <- sFloat "y"

       constrain $ fpIsPoint x
       constrain $ fpIsPoint y
       constrain $ x .== y
       constrain $ x .> 0
       constrain $ fpIsPoint $ x+y

       minimize "metric-min-x+y" $ observe "min-x+y" (x+y)

{- HLint ignore module "Reduce duplication" -}
