-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.BitPrecise.Legato
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
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
 where legatoPgm = runSymbolic (True, Nothing) $ do
                       mem     <- newArray "mem" Nothing
                       addrX   <- free "addrX"
                       x       <- free "x"
                       addrY   <- free "addrY"
                       y       <- free "y"
                       addrLow <- free "addrLow"
                       regX    <- free "regX"
                       regA    <- free "regA"
                       memVals <- free "memVals"
                       flagC   <- free "flagC"
                       flagZ   <- free "flagZ"
                       output $ legatoIsCorrect mem (addrX, x) (addrY, y) addrLow (regX, regA, memVals, flagC, flagZ)
       legatoC = compileToC' "legatoMult" $ do
                    cgSetDriverValues [87, 92]
                    cgPerformRTCs True
                    x <- cgInput "x"
                    y <- cgInput "y"
                    let (hi, lo) = runLegato (0, x) (1, y) 2 (initMachine (mkSFunArray (const 0)) (0, 0, 0, false, false))
                    cgOutput "hi" hi
                    cgOutput "lo" lo
