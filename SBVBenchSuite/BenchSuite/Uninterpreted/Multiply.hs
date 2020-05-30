-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Uninterpreted.Multiply
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Uninterpreted.Multiply
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}
{-# LANGUAGE ScopedTypeVariables #-}

module BenchSuite.Uninterpreted.Multiply(benchmarks) where

import Documentation.SBV.Examples.Uninterpreted.Multiply
import Data.SBV

import BenchSuite.Bench.Bench

benchmarks :: Runner
benchmarks = rGroup
  [ run "synthMul22" synthMul22 `using` runner satWith
  , run "Correctness" correct `using` runner proveWith
  ]
  where
    mul22_hi :: SBool -> SBool -> SBool -> SBool -> SBool
    mul22_hi a1 a0 b1 b0 = ite ([a1, a0, b1, b0] .== [sFalse, sTrue , sTrue , sFalse]) sTrue
                         $ ite ([a1, a0, b1, b0] .== [sFalse, sTrue , sTrue , sTrue ]) sTrue
                         $ ite ([a1, a0, b1, b0] .== [sTrue , sFalse, sFalse, sTrue ]) sTrue
                         $ ite ([a1, a0, b1, b0] .== [sTrue , sFalse, sTrue , sTrue ]) sTrue
                         $ ite ([a1, a0, b1, b0] .== [sTrue , sTrue , sFalse, sTrue ]) sTrue
                         $ ite ([a1, a0, b1, b0] .== [sTrue , sTrue , sTrue , sFalse]) sTrue
                           sFalse

    correct = \a1 a0 b1 b0 -> mul22_hi a1 a0 b1 b0 .== (a1 .&& b0) .<+> (a0 .&& b1)
