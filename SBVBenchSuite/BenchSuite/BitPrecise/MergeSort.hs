-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.BitPrecise.MergeSort
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.BitPrecise.MergeSort
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module BenchSuite.BitPrecise.MergeSort(benchmarks) where

import Documentation.SBV.Examples.BitPrecise.MergeSort
import BenchSuite.Bench.Bench as B

import Data.SBV

-- benchmark suite
benchmarks :: Runner
benchmarks = rGroup
  [ B.run    "Correctness.MergeSort 10"   (correctness' 10)   `using` runner Data.SBV.proveWith
  , B.run    "Correctness.MergeSort 100"  (correctness' 100)  `using` runner Data.SBV.proveWith
  , B.run    "Correctness.MergeSort 1000" (correctness' 1000) `using` runner Data.SBV.proveWith
  , B.runIO  "CodeGen.MergeSort 10" $ codeGen 10
  , B.runIO  "CodeGen.MergeSort 100" $ codeGen 100
  , B.runIO  "CodeGen.MergeSort 1000" $ codeGen 1000
  ]
  where correctness' n = do xs <- mkFreeVars n
                            let ys = mergeSort xs
                            return $ nonDecreasing ys .&& isPermutationOf xs ys
