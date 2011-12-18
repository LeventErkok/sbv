-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.CRC.CCITT_Unidir
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Examples.CRC.CCITT_Unidir
-----------------------------------------------------------------------------

module TestSuite.CRC.CCITT_Unidir(testSuite) where

import Data.SBV

import Examples.CRC.CCITT_Unidir
import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "ccitHDis3" ~: assert       =<< isTheorem (crcUniGood 3)
 , "ccitHDis4" ~: assert . not =<< isTheorem (crcUniGood 4)
 ]
