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

module TestSuite.BitPrecise.PrefixSum(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.BitPrecise.PrefixSum

import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
    "prefixSum1" ~: assert =<< isThm (flIsCorrect  8 (0, (+)))
  , "prefixSum2" ~: assert =<< isThm (flIsCorrect 16 (0, smax))
  , "prefixSum3" ~: runSymbolic (True, Nothing) (genPrefixSumInstance 16 >>= output) `goldCheck` "prefixSum_16.gold"
  ]
