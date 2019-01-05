-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Crypto.AES
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.Crypto.AES
-----------------------------------------------------------------------------

module TestSuite.Crypto.AES(tests) where

import Data.SBV.Internals
import Documentation.SBV.Examples.Crypto.AES

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "Crypto.AES" [
   goldenVsStringShow "aes128Enc" $ snd <$> compileToC'    "aes128Enc" (aes128EncDec True)
 , goldenVsStringShow "aes128Dec" $ snd <$> compileToC'    "aes128Dec" (aes128EncDec False)
 , goldenVsStringShow "aes128Lib" $ snd <$> compileToCLib' "aes128Lib" aes128Comps
 ]
 where aes128EncDec d = do pt  <- cgInputArr 4 "pt"
                           key <- cgInputArr 4 "key"
                           cgSetDriverValues $ repeat 0
                           let (encKs, decKs) = aesKeySchedule key
                               res | d    = aesEncrypt pt encKs
                                   | True = aesDecrypt pt decKs
                           cgOutputArr "ct" res
       aes128Comps = [(f, setVals c) | (f, c) <- aes128LibComponents]
       setVals c = cgSetDriverValues (repeat 0) >> c
