-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.WeakestPreconditions.Sum
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.WeakestPreconditions.Sum
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}
{-# LANGUAGE NamedFieldPuns #-}

module BenchSuite.WeakestPreconditions.Sum(benchmarks) where

import Documentation.SBV.Examples.WeakestPreconditions.Sum
import Data.SBV

import Control.DeepSeq
import BenchSuite.Bench.Bench
import BenchSuite.WeakestPreconditions.Instances()

instance NFData a => NFData (SumS a)


benchmarks :: Runner
benchmarks = rGroup [ runIO "Correctness.Sum.correctInvariant"     $ correctness correctInvariant (Just measure)
                    , runIO "Correctness.Sum.alwaysFalseInvariant" $ correctness alwaysFalseInvariant Nothing
                    , runIO "Correctness.Sum.alwaysTrueInvariant"  $ correctness alwaysTrueInvariant Nothing
                    , runIO "Correctness.Sum.loopInvariant"        $ correctness loopInvariant Nothing
                    , runIO "Correctness.Sum.badMeasure1"          $ correctness badMeasure1Invariant (Just badMeasure1)
                    , runIO "Correctness.Sum.badMeasure2"          $ correctness badMeasure2Invariant (Just badMeasure2)
                    ]
             where
               correctInvariant     SumS{n, i, s} = s .== (i*(i+1)) `sDiv` 2 .&& i .<= n
               measure              SumS{n, i}    = [n - i]
               alwaysFalseInvariant _             = sFalse
               alwaysTrueInvariant  _             =  sTrue
               loopInvariant        SumS{n, i, s} = s .<= i .&& s .== (i*(i+1)) `sDiv` 2 .&& i .<= n
               badMeasure1Invariant SumS{n, i, s} = s .== (i*(i+1)) `sDiv` 2 .&& i .<= n
               badMeasure1          SumS{i}       = [- i]
               badMeasure2Invariant SumS{n, i, s} = s .== (i*(i+1)) `sDiv` 2 .&& i .<= n
               badMeasure2          SumS{n, i}    = [n + i]
