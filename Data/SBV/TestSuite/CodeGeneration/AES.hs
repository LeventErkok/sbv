-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.CodeGeneration.AES
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.CodeGeneration.AES
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.CodeGeneration.AES(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.CodeGeneration.AES

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
   "aes128Enc" ~: compileToC "aes128Enc" (aes128EncDec True)  `goldCheck` "aes128Enc.gold"
 , "aes128Dec" ~: compileToC "aes128Dec" (aes128EncDec False) `goldCheck` "aes128Dec.gold"
 ]
 where driverInputs = replicate 8 0
       aes128EncDec d = do pt  <- cgInputArr 4 "pt"
                           key <- cgInputArr 4 "key"
                           cgSetDriverValues $ repeat 0
                           let (encKs, decKs) = aesKeySchedule key
                               res | d    = aesEncrypt pt encKs
                                   | True = aesDecrypt pt decKs
                           cgOutputArr "ct" res
