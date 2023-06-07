-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Crypto.AES
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.Crypto.AES
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Crypto.AES(tests) where

import Data.SBV.Internals
import Documentation.SBV.Examples.Crypto.AES

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "Crypto.AES" [
   goldenVsStringShow "aes128Enc" $ thd <$> compileToC'    "aes128Enc" (aes128EncDec True)
 , goldenVsStringShow "aes128Dec" $ thd <$> compileToC'    "aes128Dec" (aes128EncDec False)
 , goldenVsStringShow "aes128Lib" $ thd <$> compileToCLib' "aes128Lib" aes128Comps
 ]
 where aes128EncDec d = do pt  <- cgInputArr 4 "pt"
                           key <- cgInputArr 4 "key"
                           cgSetDriverValues $ repeat 0
                           let (encKs, decKs) = aesKeySchedule key
                               res | d    = aesEncrypt pt encKs
                                   | True = aesDecrypt pt decKs
                           cgOutputArr "ct" res
       aes128Comps = [(f, setVals c) | (f, _, c) <- aesLibComponents 128]
       setVals c = cgSetDriverValues (repeat 0) >> c
       thd (_, _, r) = r
