-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Puzzles.Counts
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Documentation.SBV.Examples.Puzzles.Counts
-----------------------------------------------------------------------------

module TestSuite.Puzzles.Counts(tests) where

import Documentation.SBV.Examples.Puzzles.Counts

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "Puzzles.Counts" [
  goldenVsStringShow "counts" countPgm
 ]
 where countPgm = runSAT $ forAll_ puzzle' >>= output
       puzzle' d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 = puzzle [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9]
