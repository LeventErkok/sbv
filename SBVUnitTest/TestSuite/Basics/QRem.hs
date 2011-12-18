-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Basics.QRem
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Examples.Basics.QRem
-----------------------------------------------------------------------------

module TestSuite.Basics.QRem(testSuite) where

import Data.SBV

import Examples.Basics.QRem
import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "qrem" ~: assert =<< isTheorem (qrem :: SWord8 -> SWord8 -> SBool)
 ]
