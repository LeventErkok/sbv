-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Puzzles.MagicSquare
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Puzzles.MagicSquare
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Puzzles.MagicSquare(benchmarks) where

import Documentation.SBV.Examples.Puzzles.MagicSquare

import Utils.SBVBenchFramework
import BenchSuite.Bench.Bench as S


-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
  [ S.run "MagicSquare.magic 2" (mkMagic 2) `using` runner allSatWith
  , S.run "MagicSquare.magic 3" (mkMagic 3) `using` runner allSatWith
  ]

mkMagic :: Int -> Symbolic SBool
mkMagic n = (isMagic . chunk n) `fmap` mkFreeVars (n*n)
