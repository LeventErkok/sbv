-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.WeakestPreconditions.Fig
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.WeakestPreconditions.Fig
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module BenchSuite.WeakestPreconditions.Fib(benchmarks) where

import Documentation.SBV.Examples.WeakestPreconditions.Fib
import Data.SBV.Tools.WeakestPreconditions

import Control.DeepSeq
import BenchSuite.Bench.Bench
import BenchSuite.WeakestPreconditions.Instances()

instance NFData a => NFData (FibS a)


benchmarks :: Runner
benchmarks = rGroup
  [ runIO "Correctness.Fib" correctness
  , runIO "ImperativeFib" $ traceExecution imperativeFib $ FibS {n = 3, i = 0, k = 0, m = 0}
  ]
