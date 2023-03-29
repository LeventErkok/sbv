-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Optimization.Reals
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for optimization routines, reals
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Optimization.Reals(tests) where

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Optimization.Reals"
    [ goldenVsStringShow "optReal1" (optimize Lexicographic p)
    ]

p :: ConstraintSet
p = do x <- sReal "x"
       y <- sReal "y"
       z <- sReal "z"
       w <- sReal "w"

       constrain $ x .>= 0
       constrain $ y .>= 0
       constrain $ z .>= 0
       constrain $ w .>= 0

       constrain $ x + y + z + w .<= 40
       constrain $ 2 * x + y - z - w .>= 10
       constrain $ w - y .>= 10

       maximize "p" $ 0.5 * x + 3 * y + z + 4 * w
