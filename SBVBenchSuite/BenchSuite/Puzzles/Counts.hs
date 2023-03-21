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
import BenchSuite.Bench.Bench as S


-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup [ S.run "Counts" countPgm ]
 where countPgm = puzzle `fmap` mkFreeVars 10
