-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Queries.GuessNumber
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Queries.GuessNumber
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module BenchSuite.Queries.GuessNumber(benchmarks) where

import Documentation.SBV.Examples.Queries.GuessNumber

import BenchSuite.Bench.Bench

benchmarks :: Runner
benchmarks =  runIO "GuessNumber.play" play
