-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.TestSuite.Uninterpreted
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.Uninterpreted.Uninterpreted
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.Uninterpreted.Uninterpreted where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.Uninterpreted.Uninterpreted

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "uninterpreted-0" ~: assert       =<< isTheorem p0
 , "uninterpreted-1" ~: assert       =<< isTheorem p1
 , "uninterpreted-2" ~: assert . not =<< isTheorem p2
 ]
