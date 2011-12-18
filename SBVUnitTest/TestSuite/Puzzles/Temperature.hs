-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Puzzles.Temperature
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Examples.Puzzles.Temperature
-----------------------------------------------------------------------------

module TestSuite.Puzzles.Temperature(testSuite) where

import Data.SBV

import Examples.Puzzles.Temperature
import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
  "temperature" ~: sat (revOf `fmap` exists_) `goldCheck` "temperature.gold"
 ]
