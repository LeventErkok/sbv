-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.BitPrecise.PrefixSum
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Data.SBV.Examples.PrefixSum.PrefixSum
-----------------------------------------------------------------------------

module TestSuite.BitPrecise.PrefixSum(tests) where

import Data.SBV
import Data.SBV.Examples.BitPrecise.PrefixSum

import SBVTest

-- Test suite
tests :: TestTree
tests =
  testGroup "BitPrecise.PrefixSum"
    [
        testCase "prefixSum1" (assertIsThm (flIsCorrect  8 (0, (+))))
      , testCase "prefixSum2" (assertIsThm (flIsCorrect 16 (0, smax)))
    ]
