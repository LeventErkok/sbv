-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.BitPrecise.Legato
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.BitPrecise.Legato
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.BitPrecise.Legato(tests) where

import Data.SBV.Internals hiding (free, output)
import Documentation.SBV.Examples.BitPrecise.Legato

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "BitPrecise.Legato" [
   goldenVsStringShow "legato"   legatoPgm
 , goldenVsStringShow "legato_c" legatoC
 ]
 where legatoPgm = runSAT $ do
                       x     <- free "x"
                       y     <- free "y"
                       lo    <- free "lo"
                       regX  <- free "regX"
                       regA  <- free "regA"
                       flagC <- free "flagC"
                       flagZ <- free "flagZ"
                       pure $ legatoIsCorrect (x, y, lo, regX, regA, flagC, flagZ)

       thd (_, _, r) = r

       legatoC = thd <$> compileToC' "legatoMult" (do
                    cgSetDriverValues [87, 92]
                    x <- cgInput "x"
                    y <- cgInput "y"
                    let (hi, lo) = runLegato (initMachine (x, y, 0, 0, 0, sFalse, sFalse))
                    cgOutput "hi" hi
                    cgOutput "lo" lo)
