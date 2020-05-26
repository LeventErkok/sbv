-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Misc.Polynomials
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Misc.Polynomials
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Misc.Polynomials(benchmarks) where

import Documentation.SBV.Examples.Misc.Polynomials

import BenchSuite.Bench.Bench


-- benchmark suite
benchmarks :: Runner
benchmarks =  runIO "testGF28 " testGF28
