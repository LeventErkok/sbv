-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Arrays.Memory
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Examples.Arrays.Memory
-----------------------------------------------------------------------------

module TestSuite.Arrays.Memory(testSuite) where

import Examples.Arrays.Memory
import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
     "memory-raw"           ~: assert       =<< isThm raw
   , "memory-waw"           ~: assert       =<< isThm waw
   , "memory-wcommute-bad"  ~: assert . not =<< isThm wcommutesBad
   , "memory-wcommute-good" ~: assert       =<< isThm wcommutesGood
   ]
