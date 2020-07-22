-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.ProofTools.Sum
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.ProofTools.Sum
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module BenchSuite.ProofTools.Sum(benchmarks) where

import Control.DeepSeq

import Data.SBV.Tools.Induction
import Documentation.SBV.Examples.ProofTools.Sum

import BenchSuite.Bench.Bench as B

-- benchmark suite
benchmarks :: Runner
benchmarks = runIO "Sum.Correctness" sumCorrect

instance NFData a => NFData (S a)
instance NFData a => NFData (InductionResult a) where rnf a = seq a ()
