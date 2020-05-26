-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.CodeGeneration.Fibonacci
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.CodeGeneration.Fibonacci
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.CodeGeneration.Fibonacci(benchmarks) where

import Documentation.SBV.Examples.CodeGeneration.Fibonacci

import BenchSuite.Bench.Bench

-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
  [ runIO "Fib1 1"  $ genFib1 1
  , runIO "Fib1 10" $ genFib1 10
  , runIO "Fib1 20" $ genFib1 20
  , runIO "Fib2 1"  $ genFib1 1
  , runIO "Fib2 10" $ genFib1 10
  , runIO "Fib2 20" $ genFib1 20
  ]
