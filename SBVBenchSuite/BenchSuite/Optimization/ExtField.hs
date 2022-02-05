-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Optimization.ExtField
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Optimization.ExtField
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Optimization.ExtField(benchmarks) where

import Documentation.SBV.Examples.Optimization.ExtField
import BenchSuite.Bench.Bench as B
import BenchSuite.Optimization.Instances()

import Data.SBV


-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
             [ run "ExtField.problem" problem `using` runner (`optimizeWith` Lexicographic)
             ]
