-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Strings.SQLInjection
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Strings.SQLInjection
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Strings.SQLInjection(benchmarks) where

import Documentation.SBV.Examples.Strings.SQLInjection
import Data.List

import BenchSuite.Bench.Bench

-- benchmark suite
benchmarks :: Runner
benchmarks =  rGroup
  [ runIO "FindInjection" $ ("'; DROP TABLE 'users" `Data.List.isSuffixOf`) <$> findInjection exampleProgram
  ]
