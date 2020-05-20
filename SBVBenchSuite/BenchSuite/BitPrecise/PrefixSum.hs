-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.BitPrecise.PrefixSum
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.BitPrecise.PrefixSum
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.BitPrecise.PrefixSum(benchmarks) where

import Documentation.SBV.Examples.BitPrecise.PrefixSum
import BenchSuite.Bench.Bench as B

import Data.SBV

-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
  [ B.run    "Correctness.PrefixSum 8"  (flIsCorrect 8  (0,(+)))  `using` runner proveWith
  , B.run    "Correctness.PrefixSum 16" (flIsCorrect 16 (0,smax)) `using` runner proveWith
  ]
