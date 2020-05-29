-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Queries.Interpolants
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Queries.Interpolants
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Queries.Interpolants(benchmarks) where

import Documentation.SBV.Examples.Queries.Interpolants

import BenchSuite.Bench.Bench

import Data.SBV

benchmarks :: Runner
benchmarks =  runIO "Interpolants.evenOdd" $ runSMT evenOdd
