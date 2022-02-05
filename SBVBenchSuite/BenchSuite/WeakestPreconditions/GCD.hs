-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.WeakestPreconditions.GCD
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.WeakestPreconditions.GCD
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module BenchSuite.WeakestPreconditions.GCD(benchmarks) where

import Documentation.SBV.Examples.WeakestPreconditions.GCD
import Data.SBV.Tools.WeakestPreconditions

import Control.DeepSeq
import BenchSuite.Bench.Bench
import BenchSuite.WeakestPreconditions.Instances()

instance NFData a => NFData (GCDS a)


benchmarks :: Runner
benchmarks = rGroup
  [ runIO "Correctness.GCD" correctness
  , runIO "ImperativeGCD" $ traceExecution imperativeGCD $ GCDS {x = 14, y = 4, i = 0, j = 0}
  ]
