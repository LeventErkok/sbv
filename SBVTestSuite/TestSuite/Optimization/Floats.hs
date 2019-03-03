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
    [ goldenVsStringShow "optFloat1" (optimizeWith z3{printBase=16} Independent (p True))
    , goldenVsStringShow "optFloat2" (optimizeWith z3{printBase=16} Independent (p False))
    ]

p :: Bool -> Goal
p reqPoint = do x <- sFloat  "x"
                y <- sDouble "y"

                when reqPoint $ do constrain $ fpIsPoint x
                                   constrain $ fpIsPoint y

                minimize "min-x" x
                maximize "max-x" x
                minimize "min-y" y
                maximize "max-y" y
