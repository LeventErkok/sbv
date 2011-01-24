-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.PrefixSum.PrefixSum
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.PrefixSum.PrefixSum
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.PrefixSum.PrefixSum(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.PrefixSum.PrefixSum

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck ->
   let genSize i = runSymbolic (genPrefixSumInstance i) `goldCheck` ("prefixSum_" ++ show i ++ ".gold")
   in test [
        "prefixSum1" ~: assert =<< isTheorem (flIsCorrect  8 (0, (+)))
      , "prefixSum2" ~: assert =<< isTheorem (flIsCorrect 16 (0, smax))
      , "prefixSum3" ~: genSize 4
      , "prefixSum4" ~: genSize 16
      ]
