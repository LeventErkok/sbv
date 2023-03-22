-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CRC.CCITT
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Examples.CRC.CCITT
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CRC.CCITT(tests) where

import Data.SBV.Tools.Polynomial
import Utils.SBVTestFramework

import Data.Proxy

-- Test suite
tests :: TestTree
tests = testGroup "CRC.CCITT"
  [ goldenVsStringShow "ccitt" crcPgm
  , testCase "ccit_good" (assertIsThm crcGood)
  ]
  where crcPgm = runSAT $ crcGood <$> free_ <*> free_

extendData :: SWord 48 -> SWord 64
extendData msg = fromBitsBE $ blastBE msg ++ replicate 16 sFalse

mkFrame :: SWord 48 -> SWord 64
mkFrame msg = msg # crc_48_16 msg

crc_48_16 :: SWord 48 -> SWord 16
crc_48_16 msg = res
  where msg64, divisor :: SWord 64
        msg64   = extendData msg
        divisor = polynomial [16, 12, 5, 0]
        crc64 = pMod msg64 divisor
        res   = bvExtract (Proxy @15) (Proxy @0) crc64

diffCount :: SWord 64 -> SWord 64 -> SWord8
diffCount x y = count $ zipWith (.==) (blastLE x) (blastLE y)
  where count []     = 0
        count (b:bs) = let r = count bs in ite b r (1+r)

-- Claim: If there is an undetected corruption, it must be at least at 4 bits; i.e. HD is 4
crcGood :: SWord 48 -> SWord 48 -> SBool
crcGood sent received =
     sent ./= received .=> diffCount frameSent frameReceived .> 3
   where frameSent     = mkFrame sent
         frameReceived = mkFrame received
