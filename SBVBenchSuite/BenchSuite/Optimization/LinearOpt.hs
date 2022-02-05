-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Optimization.LinearOpt
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Optimization.LinearOpt
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Optimization.LinearOpt(benchmarks) where

import Documentation.SBV.Examples.Optimization.LinearOpt
import BenchSuite.Bench.Bench as B
import BenchSuite.Optimization.Instances()

import Data.SBV


-- benchmark suite
benchmarks :: Runner
benchmarks = run "LinearOpt.problem" problem `using` runner (`optimizeWith` Lexicographic)
