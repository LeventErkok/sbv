-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CRC.GenPoly
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Examples.CRC.GenPoly
-----------------------------------------------------------------------------

module TestSuite.CRC.GenPoly(tests) where

import Data.SBV.Tools.Polynomial
import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "CRC.GenPoly"
    [ testCase "crcGoodE" (assertIsSat crcGoodE)
    , testCase "crcGood"  (assertIsntThm (crcGood 3 12))
    ]

crcGoodE :: Symbolic SBool
crcGoodE = do
  x1 <- exists_
  x2 <- exists_
  y1 <- exists_
  y2 <- exists_
  return (crcGood 3 0 (x1,x2) (y1,y2))

-- We don't have native support for 48 bits in Data.SBV
-- So, represent as 32 high-bits and 16 low
type SWord48 = (SWord32, SWord16)

extendData :: SWord48 -> SWord64
extendData (h, l) = h # l # 0

mkFrame :: SWord64 -> SWord48 -> SWord64
mkFrame poly msg@(h, l) = h # l # crc_48_16 msg poly

crc_48_16 :: SWord48 -> SWord64 -> SWord16
crc_48_16 msg poly = res
  where msg64 = extendData msg
        crc64 = pMod msg64 poly
        (_, res) = split (snd (split crc64))

diffCount :: SWord64 -> SWord64 -> SWord8
diffCount x y = count $ zipWith (.==) (blastLE x) (blastLE y)
  where count []     = 0
        count (b:bs) = let r = count bs in ite b r (1+r)

crcGood :: SWord8 -> SWord16 -> SWord48 -> SWord48 -> SBool
crcGood hd divisor sent received =
     sent ./= received .=> diffCount frameSent frameReceived .> hd
   where frameSent     = mkFrame poly sent
         frameReceived = mkFrame poly received
         poly          = mkPoly divisor

mkPoly :: SWord16 -> SWord64
mkPoly d = 0 # 1 # d

{-# ANN crc_48_16 ("HLint: ignore Use camelCase" :: String) #-}
