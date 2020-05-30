-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.ProofTools.Strengthen
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.ProofTools.Strengthen
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module BenchSuite.ProofTools.Strengthen(benchmarks) where

import Control.DeepSeq

import Data.SBV.Tools.Induction
import Documentation.SBV.Examples.ProofTools.Strengthen

import BenchSuite.Bench.Bench as B

-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
  [ runIO "ex1" ex1
  , runIO "ex2" ex2
  , runIO "ex3" ex3
  , runIO "ex4" ex4
  , runIO "ex5" ex5
  , runIO "ex6" ex6
  ]

instance NFData a => NFData (S a)               where rnf a = seq a ()
instance NFData a => NFData (InductionResult a) where rnf a = seq a ()
