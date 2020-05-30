-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Misc.ModelExtract
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Misc.ModelExtract
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Misc.ModelExtract(benchmarks) where

import Documentation.SBV.Examples.Misc.ModelExtract

import BenchSuite.Bench.Bench


-- benchmark suite
benchmarks :: Runner
benchmarks =  runIO "genVals" genVals
