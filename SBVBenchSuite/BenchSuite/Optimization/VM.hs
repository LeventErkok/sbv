-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Optimization.VM
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Optimization.VM
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Optimization.VM(benchmarks) where

import Documentation.SBV.Examples.Optimization.VM
import BenchSuite.Bench.Bench as B
import BenchSuite.Optimization.Instances()

import Data.SBV


-- benchmark suite
benchmarks :: Runner
benchmarks = run "VM.allocate" allocate `using` runner (`optimizeWith` Lexicographic)
