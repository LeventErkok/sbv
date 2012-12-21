-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.CRC.GenPoly
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Examples.CRC.GenPoly
-----------------------------------------------------------------------------

module TestSuite.CRC.GenPoly(testSuite) where

import Data.SBV

import Examples.CRC.GenPoly
import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "crcGood" ~: assert       =<< isSat crcGoodE
 , "crcGood" ~: assert . not =<< isThm (crcGood 3 12)
 ]
 where crcGoodE = do x1 <- exists_
                     x2 <- exists_
                     y1 <- exists_
                     y2 <- exists_
                     return (crcGood 3 0 (x1,x2) (y1,y2))
