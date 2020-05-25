-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.BitPrecise.Legato
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.BitPrecise.Legato
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.BitPrecise.Legato(benchmarks) where

import Documentation.SBV.Examples.BitPrecise.Legato
import BenchSuite.Bench.Bench as B

import Data.SBV

-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
  [ B.run    "Correctness.Legato" correctnessThm `using` runner Data.SBV.proveWith
  , B.runIO  "CodeGen.Legato" legatoInC
  ]
  where correctnessThm = do
          lo <- sWord "lo"

          x <- sWord  "x"
          y <- sWord  "y"

          regX  <- sWord "regX"
          regA  <- sWord "regA"

          flagC <- sBool "flagC"
          flagZ <- sBool "flagZ"

          return $ legatoIsCorrect (x, y, lo, regX, regA, flagC, flagZ)
