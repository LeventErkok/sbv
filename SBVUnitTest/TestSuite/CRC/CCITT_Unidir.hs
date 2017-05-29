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

module TestSuite.CRC.CCITT_Unidir(tests) where

import Examples.CRC.CCITT_Unidir
import SBVTest

-- Test suite
tests :: TestTree
tests =
  testGroup "CCITT_Unidir"
    [   testCase "ccitHDis3" (assertIsThm (crcUniGood 3))
      , testCase "ccitHDis4" (assertIsntThm (crcUniGood 4))
    ]
