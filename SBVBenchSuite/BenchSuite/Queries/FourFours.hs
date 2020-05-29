-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Queries.FourFours
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Queries.FourFours
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Queries.FourFours(benchmarks) where

import Documentation.SBV.Examples.Queries.FourFours

import BenchSuite.Bench.Bench

benchmarks :: Runner
benchmarks =  runIO "FourFours.puzzle" puzzle
