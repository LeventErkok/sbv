-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.CRC.CCITT_Unidir
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Examples.CRC.CCITT_Unidir
-----------------------------------------------------------------------------

module TestSuite.CRC.CCITT_Unidir(testSuite) where

import Examples.CRC.CCITT_Unidir
import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "ccitHDis3" ~: assert       =<< isThm (crcUniGood 3)
 , "ccitHDis4" ~: assert . not =<< isThm (crcUniGood 4)
 ]
