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
                       mem     <- newArray "mem"
                       output $ legatoIsCorrect mem (addrX, x) (addrY, y) addrLow (regX, regA, flagC, flagZ)
       legatoC = snd <$> compileToC' "legatoMult" (do
                    cgSetDriverValues [87, 92]
                    let f1Addr  = 0
                        f2Addr  = 1
                        lowAddr = 2
                    cgPerformRTCs True
                    x <- cgInput "x"
                    y <- cgInput "y"
                    memUninit <- cgSym $ newArray "mem"
                    -- Strictly speaking, initializing the lowAddr location
                    -- to 0 isn't required. But not having an initial value
                    -- there causes SBV to create an uninterpreted reference
                    -- (correctly), but undesirably!
                    let mem      = writeArray memUninit lowAddr 0
                        (hi, lo) = runLegato (f1Addr, x) (f2Addr, y) lowAddr (initMachine mem (0, 0, false, false))
                    cgOutput "hi" hi
                    cgOutput "lo" lo)
