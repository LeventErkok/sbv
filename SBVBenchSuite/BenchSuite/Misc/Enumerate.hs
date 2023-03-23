-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Misc.Enumerate
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Misc.Enumerate
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}
{-# LANGUAGE ScopedTypeVariables #-}

module BenchSuite.Misc.Enumerate(benchmarks) where

import Documentation.SBV.Examples.Misc.Enumerate

import BenchSuite.Bench.Bench
import Utils.SBVBenchFramework


-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
             [ run "Elts" _elts `using` runner allSatWith
             , run "Four" _four
             , run "MaxE" _maxE
             , run "MinE" _minE
             ]
  where _elts = \(x::SE) -> x .== x
        _four = \a b c (d::SE) -> distinct [a, b, c, d]
        _maxE = do mx <- free "maxE"
                   constrain $ \(Forall e) -> mx .>= (e::SE)
        _minE = do mx <- free "minE"
                   constrain $ \(Forall e) -> mx .<= (e::SE)
