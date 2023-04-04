-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Puzzles.Garden
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Puzzles.Garden
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror  #-}
{-# LANGUAGE OverloadedStrings #-}

module BenchSuite.Puzzles.Garden(benchmarks) where

import Data.List (isSuffixOf)

import Documentation.SBV.Examples.Puzzles.Garden

import Utils.SBVBenchFramework
import BenchSuite.Bench.Bench as S


-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup [ S.runWith s "Garden" puzzle `using` runner allSatWith ]
  where s = z3{allSatTrackUFs = False, isNonModelVar = ("_modelIgnore" `isSuffixOf`)}
