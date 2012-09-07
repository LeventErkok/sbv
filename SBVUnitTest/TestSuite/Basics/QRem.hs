-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Basics.QRem
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
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
   "qremW8" ~: assert =<< isTheorem (qrem :: SWord8   -> SWord8   -> SBool)
 , "qremI8" ~: assert =<< isTheorem (qrem :: SInt8    -> SInt8    -> SBool)
 , "qremI"  ~: assert =<< isTheorem (qrem :: SInteger -> SInteger -> SBool)
 ]
