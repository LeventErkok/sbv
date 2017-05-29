-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.BitPrecise.BitTricks
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Data.SBV.Examples.BitPrecise.BitTricks
-----------------------------------------------------------------------------

module TestSuite.BitPrecise.BitTricks(tests) where

import Data.SBV.Examples.BitPrecise.BitTricks

import SBVTest

tests :: TestTree
tests =
  testGroup "BitPrecise.BitTricks"
    [ testCase "fast min" (assertIsThm fastMinCorrect)
    , testCase "fast max" (assertIsThm fastMaxCorrect)
    , testCase "opposite signs" (assertIsThm oppositeSignsCorrect)
    , testCase "conditional set clear" (assertIsThm conditionalSetClearCorrect)
    , testCase "power of two" (assertIsThm powerOfTwoCorrect)
    ]
