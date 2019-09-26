-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Puzzles.Counts
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Puzzles.Counts
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Puzzles.Counts(benchmarks) where

import Documentation.SBV.Examples.Puzzles.Counts

import Utils.SBVBenchFramework
import BenchSuite.Overhead.SBVOverhead


-- benchmark suite
benchmarks :: Runner
benchmarks = runner "Counts" countPgm `using` setRunner allSatWith
 where countPgm = forAll_ puzzle' >>= return -- avoiding 'output' here again
       puzzle' d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 = puzzle [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9]
