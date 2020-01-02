-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CodeGeneration.CRC_USB5
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.CodeGeneration.CRC_USB5
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CodeGeneration.CRC_USB5(tests) where

import Data.SBV.Internals
import Documentation.SBV.Examples.CodeGeneration.CRC_USB5

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "CRC.CodeGen" [
   goldenVsStringShow "crcUSB5_1" $ genC crcUSB
 , goldenVsStringShow "crcUSB5_2" $ genC crcUSB'
 ]
 where thd (_, _, r) = r
       genC f = thd <$> compileToC' "crcUSB5" (do
                   cgSetDriverValues [0xFEDC]
                   msg <- cgInput "msg"
                   cgReturn $ f msg)
