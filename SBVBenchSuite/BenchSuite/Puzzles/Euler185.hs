-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Puzzles.Euler185
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Puzzles.Euler185
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Puzzles.Euler185(benchmarks) where

import Documentation.SBV.Examples.Puzzles.Euler185

import Utils.SBVBenchFramework
import BenchSuite.Bench.Bench as S


-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup [ S.run "Euler185" euler185 `using` runner satWith ]
