-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Strings.RegexCrossword
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Strings.RegexCrossword
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Strings.RegexCrossword(benchmarks) where

import Documentation.SBV.Examples.Strings.RegexCrossword

import BenchSuite.Bench.Bench

-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
             [ runIO "puzzle1" puzzle1
             , runIO "puzzle2" puzzle2
             , runIO "puzzle3" puzzle3
             ]
