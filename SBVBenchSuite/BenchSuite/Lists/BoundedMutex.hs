-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Lists.BoundedMutex
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Lists.BoundedMutex
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Lists.BoundedMutex(benchmarks) where

import Documentation.SBV.Examples.Lists.BoundedMutex

import BenchSuite.Bench.Bench

-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
             [ runIO "CheckMutex.1"  $ checkMutex 1
             , runIO "CheckMutex.10" $ checkMutex 10
             , runIO "CheckMutex.20" $ checkMutex 20
             , runIO "NotFair.1"     $ notFair 1
             , runIO "NotFair.10"    $ notFair 10
             , runIO "NotFair.20"    $ notFair 20
             ]
