-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.WeakestPreconditions.Length
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.WeakestPreconditions.Length
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module BenchSuite.WeakestPreconditions.Length(benchmarks) where

import Documentation.SBV.Examples.WeakestPreconditions.Length

import BenchSuite.Bench.Bench
import BenchSuite.WeakestPreconditions.Instances()

benchmarks :: Runner
benchmarks = runIO "Correctness.Length" correctness
