-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.CRC.Parity
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.CRC.Parity
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.CRC.Parity(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.CRC.Parity

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "parity" ~: assert =<< isTheorem parityOK
 ]
