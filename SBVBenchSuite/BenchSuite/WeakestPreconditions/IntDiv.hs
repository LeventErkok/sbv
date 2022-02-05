-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.WeakestPreconditions.IntDiv
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.WeakestPreconditions.IntDiv
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module BenchSuite.WeakestPreconditions.IntDiv(benchmarks) where

import Documentation.SBV.Examples.WeakestPreconditions.IntDiv

import Control.DeepSeq
import BenchSuite.Bench.Bench
import BenchSuite.WeakestPreconditions.Instances()

instance NFData a => NFData (DivS a)


benchmarks :: Runner
benchmarks = runIO "Correctness.IntDiv" correctness
