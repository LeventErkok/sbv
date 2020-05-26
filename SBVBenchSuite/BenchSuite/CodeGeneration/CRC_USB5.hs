-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.CodeGeneration.CRC_USB5
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.CodeGeneration.CRC_USB5
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.CodeGeneration.CRC_USB5(benchmarks) where

import Documentation.SBV.Examples.CodeGeneration.CRC_USB5

import BenchSuite.Bench.Bench

-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
  [ runIO "Correctness" crcGood
  , runIO "CodeGen 1" cg1
  , runIO "CodeGen 2" cg2
  ]
