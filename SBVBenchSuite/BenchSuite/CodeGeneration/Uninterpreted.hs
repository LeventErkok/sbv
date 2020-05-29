-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.CodeGeneration.Uninterpreted
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.CodeGeneration.Uninterpreted
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.CodeGeneration.Uninterpreted(benchmarks) where

import Documentation.SBV.Examples.CodeGeneration.Uninterpreted
import Data.SBV

import BenchSuite.Bench.Bench

-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
  [ run "Correctness" testLeft `using` runner proveWith
  , runIO "CodeGen" genCCode
  ]
  where testLeft = \x y -> tstShiftLeft x y 0 .== x + y
