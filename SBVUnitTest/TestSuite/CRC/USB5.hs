-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.CRC.USB5
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Examples.CRC.USB5
-----------------------------------------------------------------------------

module TestSuite.CRC.USB5(testSuite) where

import Data.SBV

import Examples.CRC.USB5
import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "usbGood" ~: assert =<< isTheorem usbGood
 ]
