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
   "legato-1" ~: legatoPgm `goldCheck` "legato.gold"
 , "legato-2" ~: compileToC' [87, 92] True "legatoMult" ["x", "y", "hi", "lo"] cg_runLegato `goldCheck` "legato_c.gold"
 ]
 where legatoPgm = runSymbolic $ forAll ["mem", "addrX", "x", "addrY", "y", "addrLow", "regX", "regA", "memVals", "flagC", "flagZ"] legatoIsCorrect
                                 >>= output
