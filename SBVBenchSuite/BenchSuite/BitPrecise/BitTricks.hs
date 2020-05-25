-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.BitPrecise.BitTricks
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.BitPrecise.BitTricks
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.BitPrecise.BitTricks(benchmarks) where

import Documentation.SBV.Examples.BitPrecise.BitTricks
import BenchSuite.Bench.Bench as B

import Data.SBV (proveWith)

-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
  [ B.run "Fast-min" fastMinCorrect `using` runner proveWith
  , B.run  "Fast-max" fastMaxCorrect `using` runner proveWith
  ]
