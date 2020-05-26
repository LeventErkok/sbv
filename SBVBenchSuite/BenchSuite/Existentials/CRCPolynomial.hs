-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Existentials.CRCPolynomial
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Existentials.CRCPolynomial
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Existentials.CRCPolynomial(benchmarks) where

import Documentation.SBV.Examples.Existentials.CRCPolynomial

import BenchSuite.Bench.Bench

-- benchmark suite
benchmarks :: Runner
benchmarks =  runIO "FindPolynomials" findHD4Polynomials
