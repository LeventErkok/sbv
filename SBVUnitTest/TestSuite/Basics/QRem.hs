-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Basics.QRem
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Examples.Basics.QRem
-----------------------------------------------------------------------------

module TestSuite.Basics.QRem(tests) where

import Data.SBV

import Examples.Basics.QRem
import SBVTest

tests :: TestTree
tests =
  testGroup "Basics.QRem"
    [ testCase "qremW8" (assertIsThm (qrem :: SWord8   -> SWord8   -> SBool))
    , testCase "qremI8" (assertIsThm (qrem :: SInt8    -> SInt8    -> SBool))
    , testCase "qremI" (assertIsThm (qrem :: SInteger -> SInteger -> SBool))
    ]
