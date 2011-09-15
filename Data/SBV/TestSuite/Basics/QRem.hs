-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.Basics.QRem
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.Basics.QRem
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.Basics.QRem(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.Basics.QRem

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "qrem" ~: assert =<< isTheorem (qrem :: SWord8 -> SWord8 -> SBool)
 ]
