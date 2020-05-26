-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Lists.Fibonacci
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Lists.Fibonacci
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Lists.Fibonacci(benchmarks) where

import Documentation.SBV.Examples.Lists.Fibonacci
import Data.SBV

import BenchSuite.Bench.Bench

-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
             [ runIO "GenFibs" $ runSMT genFibs
             ]
