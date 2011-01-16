-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.CRC.CCITT_Unidir
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.CRC.CCITT_Unidir
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.CRC.CCITT_Unidir(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.CRC.CCITT_Unidir

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "ccitHDis3" ~: assert       =<< isTheorem (crcUniGood 3)
 , "ccitHDis4" ~: assert . not =<< isTheorem (crcUniGood 4)
 ]
