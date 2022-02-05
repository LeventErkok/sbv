-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Optimization.Production
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Optimization.Production
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Optimization.Production(benchmarks) where

import Documentation.SBV.Examples.Optimization.Production
import BenchSuite.Bench.Bench as B
import BenchSuite.Optimization.Instances()

import Data.SBV


-- benchmark suite
benchmarks :: Runner
benchmarks = run "Production.production" production `using` runner (`optimizeWith` Lexicographic)
