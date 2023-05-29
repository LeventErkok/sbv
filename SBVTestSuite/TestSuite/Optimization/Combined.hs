-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Optimization.Combined
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for optimization routines, combined objectives
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Optimization.Combined(tests) where

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Optimization.Combined"
    [ goldenVsStringShow "combined1" (optimize Lexicographic      combined1)
    , goldenVsStringShow "combined2" (optimize Lexicographic      combined2)
    , goldenVsStringShow "pareto1"   (optimize (Pareto Nothing)   pareto1)
    , goldenVsStringShow "pareto2"   (optimize (Pareto (Just 30)) pareto2)
    , goldenVsStringShow "pareto3"   (optimize (Pareto Nothing)   pareto3)
    ]

combined1 :: ConstraintSet
combined1 = do x <- sInteger "x"
               y <- sInteger "y"
               z <- sInteger "z"

               constrain $ x .< z
               constrain $ y .< z
               constrain $ z .< 5
               constrain $ x ./= y

               maximize "max_x" x
               maximize "max_y" y

combined2 :: ConstraintSet
combined2 = do a <- sBool "a"
               b <- sBool "b"
               c <- sBool "c"

               assertWithPenalty "soft_a" a (Penalty 1 (Just "A"))
               assertWithPenalty "soft_b" b (Penalty 2 (Just "B"))
               assertWithPenalty "soft_c" c (Penalty 3 (Just "A"))

               constrain $ a .== c
               constrain $ sNot (a .&& b)

pareto1 :: ConstraintSet
pareto1 = do x <- sInteger "x"
             y <- sInteger "y"

             constrain $ 5 .>= x
             constrain $ x .>= 0
             constrain $ 4 .>= y
             constrain $ y .>= 0

             minimize "min_x"            x
             maximize "max_x_plus_y"   $ x + y
             minimize "min_y"            y

pareto2 :: ConstraintSet
pareto2 = do x <- sInteger "x"
             y <- sInteger "y"

             constrain $ 5 .>= x
             constrain $ x .>= 0

             minimize "min_x"            x
             maximize "max_y"            y
             minimize "max_x_plus_y"   $ x + y

pareto3 :: ConstraintSet
pareto3 = do x <- sInteger "x"

             constrain $ 1 .>= x
             constrain $ 0 .<= x

             minimize "min_x"            x
             maximize "max_x_plus_x"   $ x + x

{- HLint ignore module "Reduce duplication" -}
