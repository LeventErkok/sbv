-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Puzzles.Birthday
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Puzzles.Birthday
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Puzzles.Birthday(benchmarks) where

import Documentation.SBV.Examples.Puzzles.Birthday

import BenchSuite.Bench.Bench as S
import Utils.SBVBenchFramework


-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
  [ S.run "Birthday" puzzle `using` runner allSatWith
  ]
