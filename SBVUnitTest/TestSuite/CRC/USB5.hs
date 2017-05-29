-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.CRC.USB5
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Examples.CRC.USB5
-----------------------------------------------------------------------------

module TestSuite.CRC.USB5(tests) where

import Examples.CRC.USB5
import SBVTest

-- Test suite
tests :: TestTree
tests =
  testGroup "CRC.USB5"
    [ testCase "usbGood" (assertIsThm usbGood)
    ]
