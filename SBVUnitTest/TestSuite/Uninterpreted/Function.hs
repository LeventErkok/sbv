-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Uninterpreted.Function
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Testsuite for Data.SBV.Examples.Uninterpreted.Function
-----------------------------------------------------------------------------

module TestSuite.Uninterpreted.Function where

import Data.SBV
import Data.SBV.Examples.Uninterpreted.Function

import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "aufunc-0" ~: assert       =<< isTheorem thmGood
 , "aufunc-1" ~: assert . not =<< isTheorem thmBad
 ]
