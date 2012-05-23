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

import Data.SBV

import Examples.Arrays.Memory
import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
     "memory-raw"           ~: assert       =<< isTheorem raw
   , "memory-waw"           ~: assert       =<< isTheorem waw
   , "memory-wcommute-bad"  ~: assert . not =<< isTheorem wcommutesBad
   , "memory-wcommute-good" ~: assert       =<< isTheorem wcommutesGood
   ]
