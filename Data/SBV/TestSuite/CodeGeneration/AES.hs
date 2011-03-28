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
   "aes128Enc" ~: compileToC' driverInputs True "aes128Enc" [] (aes128EncDec True)  `goldCheck` "aes128Enc.gold"
 , "aes128Dec" ~: compileToC' driverInputs True "aes128Dec" [] (aes128EncDec False) `goldCheck` "aes128Dec.gold"
 ]
 where driverInputs = replicate 8 0
       aes128EncDec d (i0, i1, i2, i3, k0, k1, k2, k3) = (o0, o1, o2, o3)
          where key = [k0, k1, k2, k3]
                i   = [i0, i1, i2, i3]
                (encKS, decKS) = aesKeySchedule key
                [o0, o1, o2, o3] = if d then aesEncrypt i encKS else aesDecrypt i decKS
