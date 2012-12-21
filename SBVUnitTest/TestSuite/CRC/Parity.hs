-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.CRC.Parity
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Examples.CRC.Parity
-----------------------------------------------------------------------------

module TestSuite.CRC.Parity(testSuite) where

import Examples.CRC.Parity
import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "parity" ~: assert =<< isThm parityOK
 ]
