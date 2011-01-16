-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.CRC.CCITT
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.CRC.CCITT
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.CRC.CCITT(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.CRC.CCITT

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
  "ccitt" ~: crcPgm `goldCheck` "ccitt.gold"
 ]
 where crcPgm = runSymbolic $ forAll_ crcGood
