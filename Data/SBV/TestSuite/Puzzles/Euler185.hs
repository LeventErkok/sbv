-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.Puzzles.Euler185
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.Puzzles.Euler185
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.Puzzles.Euler185(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.Puzzles.Euler185

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
  "euler185" ~: allSat euler185 `goldCheck` "euler185.gold"
 ]
