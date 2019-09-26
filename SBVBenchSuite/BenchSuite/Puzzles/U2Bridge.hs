-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Puzzles.U2Bridge
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Puzzles.U2Bridge
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Puzzles.U2Bridge(benchmarks) where

import Documentation.SBV.Examples.Puzzles.U2Bridge

import Utils.SBVBenchFramework
import BenchSuite.Overhead.SBVOverhead


-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
  [ runner "U2Bridge_cnt1" (count 1) `using` setRunner allSatWith
  , runner "U2Bridge_cnt2" (count 2) `using` setRunner allSatWith
  , runner "U2Bridge_cnt3" (count 3) `using` setRunner allSatWith
  , runner "U2Bridge_cnt4" (count 4) `using` setRunner allSatWith
  , runner "U2Bridge_cnt6" (count 6) `using` setRunner allSatWith
  ]
  where
    act     = do b <- exists_; p1 <- exists_; p2 <- exists_; return (b, p1, p2)
    count n = isValid `fmap` mapM (const act) [1..(n::Int)]
