-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.CRC.Parity
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Examples.CRC.Parity
-----------------------------------------------------------------------------

module TestSuite.CRC.Parity(testSuite) where

import Data.SBV

import Examples.CRC.Parity
import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "parity" ~: assert =<< isTheorem parityOK
 ]
