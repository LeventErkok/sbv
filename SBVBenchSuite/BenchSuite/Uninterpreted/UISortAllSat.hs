-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Uninterpreted.UISortAllSat
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Uninterpreted.UISortAllSat
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Uninterpreted.UISortAllSat(benchmarks) where

import Documentation.SBV.Examples.Uninterpreted.UISortAllSat
import Data.SBV

import BenchSuite.Bench.Bench

benchmarks :: Runner
benchmarks =  rGroup
  [ run "genLs" genLs `using` runner allSatWith -- could be expensive
  ]
