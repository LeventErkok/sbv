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
             , runIO "CheckMutex.3"  $ checkMutex 3
             , runIO "CheckMutex.5"  $ checkMutex 5
             , runIO "NotFair.1"     $ notFair 1
             , runIO "NotFair.3"     $ notFair 3
             , runIO "NotFair.5"     $ notFair 5
             ]
