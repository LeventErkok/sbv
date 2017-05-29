-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.CRC.Parity
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Examples.CRC.Parity
-----------------------------------------------------------------------------

module TestSuite.CRC.Parity(tests) where

import Examples.CRC.Parity
import SBVTest

tests :: TestTree
tests =
  testGroup "CRC.Parity"
    [ testCase "parity" (assertIsThm parityOK)
    ]
