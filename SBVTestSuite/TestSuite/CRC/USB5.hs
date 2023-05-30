-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CRC.USB5
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Examples.CRC.USB5
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CRC.USB5(tests) where

import Data.SBV.Tools.Polynomial
import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "CRC.USB5"
    [ testCase "usbGood" (assertIsThm usbGood)
    ]

newtype SWord11 = S11 SWord16

instance EqSymbolic SWord11 where
  S11 w .== S11 w' = w .== w'

mkSWord11 :: SWord16 -> SWord11
mkSWord11 w = S11 (w .&. 0x07FF)

extendData :: SWord11 -> SWord16
extendData (S11 w) = w `shiftL` 5

mkFrame :: SWord11 -> SWord16
mkFrame w = extendData w .|. crc_11_16 w

-- crc returns 16 bits, but the first 11 are always 0
crc_11_16 :: SWord11 -> SWord16
crc_11_16 msg = crc16 .&. 0x1F -- just get the last 5 bits
  where divisor :: SWord16
        divisor = polynomial [5, 2, 0]
        crc16 = pMod (extendData msg) divisor

diffCount :: SWord16 -> SWord16 -> SWord8
diffCount x y = count $ zipWith (.==) (blastLE x) (blastLE y)
  where count []     = 0
        count (b:bs) = let r = count bs in ite b r (1+r)

-- Claim: If there is an undetected corruption, it must be at least at 3 bits
usbGood :: SWord16 -> SWord16 -> SBool
usbGood sent16 received16 =
    sent ./= received .=> diffCount frameSent frameReceived .>= 3
   where sent     = mkSWord11 sent16
         received = mkSWord11 received16
         frameSent     = mkFrame sent
         frameReceived = mkFrame received

{- HLint ignore crc_11_16 "Use camelCase" -}
