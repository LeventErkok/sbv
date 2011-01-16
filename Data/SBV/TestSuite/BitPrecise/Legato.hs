-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.BitPrecise.Legato
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.BitPrecise.Legato
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.BitPrecise.Legato(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.BitPrecise.Legato

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
  "legato" ~: legatoPgm `goldCheck` "legato.gold"
 ]
 where legatoPgm = runSymbolic $ forAll ["mem", "addrX", "x", "addrY", "y", "addrLow", "regX", "regA", "memVals", "flagC", "flagZ"] legatoIsCorrect
