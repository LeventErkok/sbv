-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.WeakestPreconditions.IntSqrt
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.WeakestPreconditions.IntSqrt
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module BenchSuite.WeakestPreconditions.IntSqrt(benchmarks) where

import Documentation.SBV.Examples.WeakestPreconditions.IntSqrt

import Control.DeepSeq
import BenchSuite.Bench.Bench
import BenchSuite.WeakestPreconditions.Instances()

instance NFData a => NFData (SqrtS a)


benchmarks :: Runner
benchmarks = runIO "Correctness.IntSqrt" correctness
