-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Puzzles.NQueens
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Puzzles.NQueens
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Puzzles.NQueens(benchmarks) where

import Documentation.SBV.Examples.Puzzles.NQueens

import Utils.SBVBenchFramework
import BenchSuite.Overhead.SBVOverhead


-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
  [ runner "NQueens.NQueens 1" (mkQueens 1) `using` setRunner allSatWith
  , runner "NQueens.NQueens 2" (mkQueens 2) `using` setRunner allSatWith
  , runner "NQueens.NQueens 3" (mkQueens 3) `using` setRunner allSatWith
  , runner "NQueens.NQueens 4" (mkQueens 4) `using` setRunner allSatWith
  , runner "NQueens.NQueens 5" (mkQueens 5) `using` setRunner allSatWith
  , runner "NQueens.NQueens 6" (mkQueens 6) `using` setRunner allSatWith
  , runner "NQueens.NQueens 7" (mkQueens 7) `using` setRunner allSatWith
  , runner "NQueens.NQueens 8" (mkQueens 8) `using` setRunner allSatWith
  ]

mkQueens :: Int -> Symbolic SBool
mkQueens n = isValid n `fmap` mkExistVars n
