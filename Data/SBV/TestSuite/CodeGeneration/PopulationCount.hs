-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.CodeGeneration.PopulationCount
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.CodeGeneration.PopulationCount
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.CodeGeneration.PopulationCount(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.CodeGeneration.PopulationCount

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
   "popCount-1" ~: compileToC' [0x0123456789ABCDEF] False "popCount" ["x", "pc"] popCount `goldCheck` "popCount1.gold"
 , "popCount-2" ~: compileToC' [0x0123456789ABCDEF] True  "popCount" ["x", "pc"] popCount `goldCheck` "popCount2.gold"
 ]
