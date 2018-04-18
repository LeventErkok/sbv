-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.BitPrecise.Legato
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Documentation.SBV.Examples.BitPrecise.Legato
-----------------------------------------------------------------------------

module TestSuite.BitPrecise.Legato(tests) where

import Data.SBV.Internals
import Documentation.SBV.Examples.BitPrecise.Legato

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "BitPrecise.Legato" [
   goldenVsStringShow "legato"   legatoPgm
 , goldenVsStringShow "legato_c" legatoC
 ]
 where legatoPgm = runSAT $ do
                       addrX   <- free "addrX"
                       x       <- free "x"
                       addrY   <- free "addrY"
                       y       <- free "y"
                       addrLow <- free "addrLow"
                       regX    <- free "regX"
                       regA    <- free "regA"
                       flagC   <- free "flagC"
                       flagZ   <- free "flagZ"
                       output $ legatoIsCorrect (mkSFunArray (const 0)) (addrX, x) (addrY, y) addrLow (regX, regA, flagC, flagZ)
       legatoC = compileToC' "legatoMult" $ do
                    cgSetDriverValues [87, 92]
                    cgPerformRTCs True
                    x <- cgInput "x"
                    y <- cgInput "y"
                    let (hi, lo) = runLegato (0, x) (1, y) 2 (initMachine (mkSFunArray (const 0)) (0, 0, false, false))
                    cgOutput "hi" hi
                    cgOutput "lo" lo
