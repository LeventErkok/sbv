-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Lists.Nested
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Lists.Nested
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Lists.Nested(benchmarks) where

import Documentation.SBV.Examples.Lists.Nested

import BenchSuite.Bench.Bench

-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
             [ runIO "Nested.Example" nestedExample
             ]
