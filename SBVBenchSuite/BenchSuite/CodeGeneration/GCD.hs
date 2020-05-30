-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.CodeGeneration.GCD
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.CodeGeneration.GCD
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.CodeGeneration.GCD(benchmarks) where

import Documentation.SBV.Examples.CodeGeneration.GCD
import Data.SBV

import BenchSuite.Bench.Bench

-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
  [ run "Correctness" sgcdIsCorrect `using` runner proveWith
  , runIO "CodeGen" genGCDInC
  ]
