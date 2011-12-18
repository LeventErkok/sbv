-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.Crypto.AES
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.Crypto.AES
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.Crypto.AES(testSuite) where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.Crypto.AES

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
   "aes128Enc" ~: compileToC'    "aes128Enc" (aes128EncDec True)  `goldCheck` "aes128Enc.gold"
 , "aes128Dec" ~: compileToC'    "aes128Dec" (aes128EncDec False) `goldCheck` "aes128Dec.gold"
 , "aes128Lib" ~: compileToCLib' "aes128Lib" aes128Comps          `goldCheck` "aes128Lib.gold"
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
