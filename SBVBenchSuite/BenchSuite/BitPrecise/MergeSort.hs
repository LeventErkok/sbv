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
  [ B.run    "Correctness.MergeSort 3"  (correctness' 3)  `using` runner Data.SBV.proveWith
  , B.run    "Correctness.MergeSort 4"  (correctness' 4)  `using` runner Data.SBV.proveWith
  , B.runIO  "CodeGen.MergeSort 3" $ codeGen 3
  , B.runIO  "CodeGen.MergeSort 4" $ codeGen 4
  ]
  where correctness' n = do xs <- mkFreeVars n
                            let ys = mergeSort xs
                            return $ nonDecreasing ys .&& isPermutationOf xs ys
