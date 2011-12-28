-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Puzzles.Counts
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.Puzzles.Counts
-----------------------------------------------------------------------------

module TestSuite.Puzzles.Counts(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.Puzzles.Counts

import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
  "counts" ~: countPgm `goldCheck` "counts.gold"
 ]
 where countPgm = runSymbolic True $ forAll_ puzzle' >>= output
       puzzle' d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 = puzzle [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9]
