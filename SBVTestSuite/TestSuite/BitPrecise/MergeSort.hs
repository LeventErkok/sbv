-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.BitPrecise.MergeSort
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.BitPrecise.MergeSort
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.BitPrecise.MergeSort(tests) where

import Data.SBV.Internals
import Documentation.SBV.Examples.BitPrecise.MergeSort

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "BitPrecise.MergeSort" [
   goldenVsStringShow "merge" mergeC
 ]
 where thd (_, _, r) = r
       mergeC = thd <$> compileToC' "merge" (do
                   cgSetDriverValues [10, 6, 4, 82, 71]
                   xs <- cgInputArr 5 "xs"
                   cgOutputArr "ys" (mergeSort xs))
