-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.Arrays.Memory
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.Arrays.Memory
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.Arrays.Memory(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.Arrays.Memory

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
     "memory-raw"           ~: assert       =<< isTheorem raw
   , "memory-waw"           ~: assert       =<< isTheorem waw
   , "memory-wcommute-bad"  ~: assert . not =<< isTheorem wcommutesBad
   , "memory-wcommute-good" ~: assert       =<< isTheorem wcommutesGood
   ]
