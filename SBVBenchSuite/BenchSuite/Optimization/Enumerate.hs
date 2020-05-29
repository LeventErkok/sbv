-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Optimization.Enumerate
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Optimization.Enumerate
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Optimization.Enumerate(benchmarks) where

import Documentation.SBV.Examples.Optimization.Enumerate
import BenchSuite.Bench.Bench as B

import BenchSuite.Optimization.Instances()

-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
  [ runIO "Enumerate.AlmostWeekend"    almostWeekend
  , runIO "Enumerate.WeekendJustOver"  weekendJustOver
  , runIO "Enumerate.firstWeekend"     firstWeekend
  ]
