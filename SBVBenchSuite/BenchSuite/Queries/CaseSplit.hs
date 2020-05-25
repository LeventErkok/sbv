-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Queries.CaseSplit
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Queries.CaseSplit
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Queries.CaseSplit(benchmarks) where

import Documentation.SBV.Examples.Queries.CaseSplit

import BenchSuite.Bench.Bench

benchmarks :: Runner
benchmarks = rGroup [ runIO "CaseSplit.1" csDemo1
                    , runIO "CaseSplit.2" csDemo2
                    ]
