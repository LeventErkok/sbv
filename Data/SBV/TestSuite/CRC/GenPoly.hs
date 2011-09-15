-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.CRC.GenPoly
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.CRC.GenPoly
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.CRC.GenPoly(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.CRC.GenPoly

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "crcGood" ~: assert       =<< isSatisfiable (crcGood 3 0)
 , "crcGood" ~: assert . not =<< isTheorem (crcGood 3 12)
 ]
