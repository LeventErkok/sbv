-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.CRC.CCITT
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Examples.CRC.CCITT
-----------------------------------------------------------------------------

module TestSuite.CRC.CCITT(testSuite) where

import Data.SBV
import Data.SBV.Internals

import Examples.CRC.CCITT
import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
  "ccitt" ~: crcPgm `goldCheck` "ccitt.gold"
 ]
 where crcPgm = runSymbolic True $ forAll_ crcGood >>= output
