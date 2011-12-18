-----------------------------------------------------------------------------
-- |
-- Module      :  Examples.TestSuite.Uninterpreted
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Examples.Uninterpreted.Uninterpreted
-----------------------------------------------------------------------------

module TestSuite.Uninterpreted.Uninterpreted where

import Data.SBV

import Examples.Uninterpreted.Uninterpreted
import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "uninterpreted-0" ~: assert       =<< isTheorem p0
 , "uninterpreted-1" ~: assert       =<< isTheorem p1
 , "uninterpreted-2" ~: assert . not =<< isTheorem p2
 ]
