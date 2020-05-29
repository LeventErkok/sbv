-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.CodeGeneration.PopulationCount
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.CodeGeneration.PopulationCount
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.CodeGeneration.PopulationCount(benchmarks) where

import Documentation.SBV.Examples.CodeGeneration.PopulationCount
import Data.SBV

import BenchSuite.Bench.Bench

-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
  [ run "Correctness" fastPopCountIsCorrect `using` runner proveWith
  , runIO "CodeGen" genPopCountInC
  ]
