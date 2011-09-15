-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.BitPrecise.PrefixSum
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.PrefixSum.PrefixSum
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.BitPrecise.PrefixSum(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.BitPrecise.PrefixSum

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
    "prefixSum1" ~: assert =<< isTheorem (flIsCorrect  8 (0, (+)))
  , "prefixSum2" ~: assert =<< isTheorem (flIsCorrect 16 (0, smax))
  , "prefixSum3" ~: runSymbolic (genPrefixSumInstance 16 >>= output) `goldCheck` "prefixSum_16.gold"
  ]
