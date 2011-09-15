-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.CRC.USB5
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.CRC.USB5
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.CRC.USB5(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.CRC.USB5

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "usbGood" ~: assert =<< isTheorem usbGood
 ]
