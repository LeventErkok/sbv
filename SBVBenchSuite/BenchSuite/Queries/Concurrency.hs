-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Queries.Concurrency
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Queries.Concurrency
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Queries.Concurrency(benchmarks) where

import Documentation.SBV.Examples.Queries.Concurrency

import BenchSuite.Bench.Bench

-- these benchmarks won't run in multithreaded mode. The benchmark target is not
-- build as -threaded
benchmarks :: Runner
benchmarks = rGroup [ runIO "Concurrency.demo"          demo
                    , runIO "Concurrency.demoDependent" demoDependent
                    ]
