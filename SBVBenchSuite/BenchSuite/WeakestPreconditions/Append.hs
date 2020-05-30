-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.WeakestPreconditions.Append
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.WeakestPreconditions.Append
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module BenchSuite.WeakestPreconditions.Append(benchmarks) where

import Documentation.SBV.Examples.WeakestPreconditions.Append

import Control.DeepSeq
import BenchSuite.Bench.Bench
import BenchSuite.WeakestPreconditions.Instances()


-- | orphaned instance for benchmarks
instance NFData a => NFData (AppC a) where rnf x = seq x ()

benchmarks :: Runner
benchmarks = runIO "Correctness.Append" correctness
