-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Puzzles.Euler185
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Data.SBV.Examples.Puzzles.Euler185
-----------------------------------------------------------------------------

module TestSuite.Puzzles.Euler185(testSuite) where

import Data.SBV
import Data.SBV.Examples.Puzzles.Euler185

import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
  "euler185" ~: allSat euler185 `goldCheck` "euler185.gold"
 ]
