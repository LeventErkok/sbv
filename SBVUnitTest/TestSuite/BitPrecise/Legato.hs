-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.BitPrecise.Legato
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.BitPrecise.Legato
-----------------------------------------------------------------------------

module TestSuite.BitPrecise.Legato(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.BitPrecise.Legato

import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
   "legato-1" ~: legatoPgm `goldCheck` "legato.gold"
 , "legato-2" ~: legatoC `goldCheck` "legato_c.gold"
 ]
 where legatoPgm = runSymbolic True $ forAll ["mem", "addrX", "x", "addrY", "y", "addrLow", "regX", "regA", "memVals", "flagC", "flagZ"] legatoIsCorrect
                                        >>= output
       legatoC = compileToC' "legatoMult" $ do
                    cgSetDriverValues [87, 92]
                    cgPerformRTCs True
                    x <- cgInput "x"
                    y <- cgInput "y"
                    let (hi, lo) = runLegato (0, x) (1, y) 2 (initMachine (mkSFunArray (const 0)) (0, 0, 0, false, false))
                    cgOutput "hi" hi
                    cgOutput "lo" lo
