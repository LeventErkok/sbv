-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.ProofTools.Fibonacci
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.ProofTools.Fibonacci
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module BenchSuite.ProofTools.Fibonacci(benchmarks) where

import Control.DeepSeq

import Data.SBV.Tools.Induction
import Documentation.SBV.Examples.ProofTools.Fibonacci

import BenchSuite.Bench.Bench as B

-- benchmark suite
benchmarks :: Runner
benchmarks =  runIO "Fibonacci.Correctness" fibCorrect


instance NFData a => NFData (S a)               where rnf a = seq a ()
instance NFData a => NFData (InductionResult a) where rnf a = seq a ()
