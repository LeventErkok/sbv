-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Crypto.AES
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Crypto.AES
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.Crypto.AES(benchmarks) where

import Documentation.SBV.Examples.Crypto.AES
import Data.SBV

import BenchSuite.Bench.Bench

-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
  [ run "InverseGF"               inverseGFPrf       `using` runner proveWith
  , run "Correctness.SBoxInverse" sboxInverseCorrect `using` runner proveWith
  , runPure "t128Enc" (fmap hex8) t128Enc
  , runPure "t128Dec" (fmap hex8) t128Dec
  , runPure "t192Enc" (fmap hex8) t192Enc
  , runPure "t192Dec" (fmap hex8) t192Dec
  , runPure "t256Enc" (fmap hex8) t256Enc
  , runPure "t256Dec" (fmap hex8) t256Dec
  , runIO   "CodeGen.AES128Lib" cgAES128Library
  ]
  where inverseGFPrf = \x -> x ./= 0 .=> x `gf28Mult` gf28Inverse x .== 1
