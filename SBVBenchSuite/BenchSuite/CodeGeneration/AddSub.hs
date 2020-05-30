-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.CodeGeneration.AddSub
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.CodeGeneration.AddSub
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.CodeGeneration.AddSub(benchmarks) where

import Documentation.SBV.Examples.CodeGeneration.AddSub

import BenchSuite.Bench.Bench

-- benchmark suite
benchmarks :: Runner
benchmarks = runIO "genAddSub" genAddSub
