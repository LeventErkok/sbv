-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Crypto.SHA
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Crypto.SHA
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Crypto.SHA(benchmarks) where

import Documentation.SBV.Examples.Crypto.SHA

import BenchSuite.Bench.Bench

-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
  [ runIO   "CodeGeneration" cgSHA256
  , runPure "knownTests 1"   knownAnswerTests 1
  , runPure "knownTests 10"  knownAnswerTests 10
  , runPure "knownTests 24"  knownAnswerTests 24
  ]
