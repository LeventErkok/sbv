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
   "popCount-1" ~: genC False `goldCheck` "popCount1.gold"
 , "popCount-2" ~: genC True  `goldCheck` "popCount2.gold"
 ]
 where genC b = compileToC' "popCount" $ do
                  cgSetDriverValues [0x0123456789ABCDEF]
                  cgPerformRTCs b
                  x <- cgInput "x"
                  cgReturn $ popCount x
