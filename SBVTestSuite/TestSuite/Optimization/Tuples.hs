-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Optimization.Tuples
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for optimization routines, tuples
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables  #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Optimization.Tuples (tests) where

import Data.SBV.Tuple
import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Optimization.Tuples"
    [ goldenVsStringShow "optTuple1" $ optimize Lexicographic t1
    ]

t1 :: ConstraintSet
t1 = do p :: STuple Integer Integer <- sTuple "p"

        constrain $ (p^._1) `inRange` (0, 100)
        constrain $ (p^._2) `inRange` (0, 100)

        constrain $ p^._1 - p^._2 .< 10
        constrain $ p^._1 + p^._2 .== 80

        maximize "max-p" p
