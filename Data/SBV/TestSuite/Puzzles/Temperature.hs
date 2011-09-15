-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.Puzzles.Temperature
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.Puzzles.Temperature
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.Puzzles.Temperature(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.Puzzles.Temperature

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
  "temperature" ~: sat revOf `goldCheck` "temperature.gold"
 ]
