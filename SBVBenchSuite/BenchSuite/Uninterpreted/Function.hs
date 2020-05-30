-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Uninterpreted.Function
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Uninterpreted.Function
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Uninterpreted.Function(benchmarks) where

import Documentation.SBV.Examples.Uninterpreted.Function
import Data.SBV

import BenchSuite.Bench.Bench

benchmarks :: Runner
benchmarks = rGroup
  [ run "thmGood" thmGood `using` runner proveWith
  ]
