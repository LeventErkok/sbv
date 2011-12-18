-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.Uninterpreted.Function
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Testsuite for Data.SBV.Examples.Uninterpreted.Function
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.Uninterpreted.Function where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.Uninterpreted.Function

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "aufunc-0" ~: assert       =<< isTheorem thmGood
 , "aufunc-1" ~: assert . not =<< isTheorem thmBad
 ]
