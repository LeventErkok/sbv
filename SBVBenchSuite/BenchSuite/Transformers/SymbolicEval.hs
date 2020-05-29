-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Transformers.SymbolicEval
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Transformers.SymbolicEval
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module BenchSuite.Transformers.SymbolicEval(benchmarks) where

import Documentation.SBV.Examples.Transformers.SymbolicEval
import Control.DeepSeq

import BenchSuite.Bench.Bench

-- benchmark suite
benchmarks :: Runner
benchmarks =  rGroup
              [ runIO "Example.1" ex1
              , runIO "Example.2" ex2
              , runIO "Example.3" ex3
              ]

instance NFData CheckResult where rnf x = seq x ()
