-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Misc.Auxiliary
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Misc.Auxiliary
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Misc.Auxiliary(benchmarks) where

import Documentation.SBV.Examples.Misc.Auxiliary

import BenchSuite.Bench.Bench as S
import Utils.SBVBenchFramework


-- benchmark suite
benchmarks :: Runner
benchmarks = S.run "Birthday" problem `using` runner allSatWith
