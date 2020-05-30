-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Queries.UnsatCore
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Queries.UnsatCore
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Queries.UnsatCore(benchmarks) where

import Documentation.SBV.Examples.Queries.UnsatCore

import BenchSuite.Bench.Bench

benchmarks :: Runner
benchmarks =  runIO "UnsatCore.ucCore" ucCore
