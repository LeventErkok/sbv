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
import Data.SBV.Examples.BitPrecise.PrefixSum

import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
    "prefixSum1" ~: assert =<< isThm (flIsCorrect  8 (0, (+)))
  , "prefixSum2" ~: assert =<< isThm (flIsCorrect 16 (0, smax))
  ]
