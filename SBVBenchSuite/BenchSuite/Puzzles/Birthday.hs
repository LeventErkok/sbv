-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Puzzles.Birthday
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Puzzles.Birthday
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Puzzles.Birthday(benchmarks) where

import Documentation.SBV.Examples.Puzzles.Birthday

import Utils.SBVBenchFramework
import BenchSuite.Overhead.SBVOverhead


-- benchmark suite
benchmarks :: Runner
benchmarks = runner "Birthday" puzzle `using` setRunner allSatWith
