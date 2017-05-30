-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Crypto.RC4
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Data.SBV.Examples.Crypto.RC4
-----------------------------------------------------------------------------

module TestSuite.Crypto.RC4(tests) where

import Data.SBV
import Data.SBV.Tools.STree
import Data.SBV.Examples.Crypto.RC4

import SBVTest

tests :: TestTree
tests =
  testGroup "Crypto.RC4"
    [ testCase "rc4swap" (assertIsThm readWrite)
    ]

readWrite :: SBV Word8 -> SBV Word8 -> SBV Bool
readWrite i j = readSTree (writeSTree initS i j) i .== j
