-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.CodeGeneration.CRC_USB5
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.CodeGeneration.CRC_USB5
-----------------------------------------------------------------------------

module TestSuite.CodeGeneration.CRC_USB5(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.CodeGeneration.CRC_USB5

import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
   "crcUSB5-1" ~: genC crcUSB  `goldCheck` "crcUSB5_1.gold"
 , "crcUSB5-2" ~: genC crcUSB' `goldCheck` "crcUSB5_2.gold"
 ]
 where genC f = compileToC' "crcUSB5" $ do
                   cgSetDriverValues [0xFEDC]
                   msg <- cgInput "msg"
                   cgReturn $ f msg
