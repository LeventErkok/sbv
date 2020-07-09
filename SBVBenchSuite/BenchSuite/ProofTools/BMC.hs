-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.ProofTools.BMC
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.ProofTools.BMC
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module BenchSuite.ProofTools.BMC(benchmarks) where

import Control.DeepSeq
import Documentation.SBV.Examples.ProofTools.BMC

import BenchSuite.Bench.Bench as B

-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
  [ runIO "BMC.ex1" ex1
  , runIO "BMC.ex2" ex2
  ]


instance NFData a => NFData (S a) where rnf a = seq a ()
