-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Misc.Tuple
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Misc.Tuple
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Misc.Tuple(benchmarks) where

import Documentation.SBV.Examples.Misc.Tuple

import BenchSuite.Bench.Bench


-- benchmark suite
benchmarks :: Runner
benchmarks =  rGroup [ runIO "Tuple" example ]
