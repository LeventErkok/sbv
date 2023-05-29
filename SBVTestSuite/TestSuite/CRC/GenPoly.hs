-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CRC.GenPoly
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Examples.CRC.GenPoly
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CRC.GenPoly(tests) where

import Data.SBV.Tools.Polynomial
import Utils.SBVTestFramework

import Data.Proxy

-- Test suite
tests :: TestTree
tests =
  testGroup "CRC.GenPoly"
    [ testCase "crcGoodE" (assertIsSat crcGoodE)
    , testCase "crcGood"  (assertIsntThm (crcGood 3 12))
    ]

crcGoodE :: Symbolic SBool
crcGoodE = pure $ quantifiedBool $ \(Exists x) (Exists y) -> crcGood 3 0 x y

extendData :: SWord 48 -> SWord 64
extendData msg = msg # 0

mkFrame :: SWord 64 -> SWord 48 -> SWord 64
mkFrame poly msg = msg # crc_48_16 msg poly

crc_48_16 :: SWord 48 -> SWord 64 -> SWord 16
crc_48_16 msg poly = res
  where msg64 = extendData msg
        crc64 = pMod msg64 poly
        res   = bvExtract (Proxy @15) (Proxy @0) crc64

diffCount :: SWord 64 -> SWord 64 -> SWord 8
diffCount x y = count $ zipWith (.==) (blastLE x) (blastLE y)
  where count []     = 0
        count (b:bs) = let r = count bs in ite b r (1+r)

crcGood :: SWord 8 -> SWord 16 -> SWord 48 -> SWord 48 -> SBool
crcGood hd divisor sent received =
     sent ./= received .=> diffCount frameSent frameReceived .> hd
   where frameSent     = mkFrame poly sent
         frameReceived = mkFrame poly received
         poly          = mkPoly divisor

mkPoly :: SWord 16 -> SWord 64
mkPoly d = 1 # d

{- HLint ignore crc_48_16 "Use camelCase" -}
{- HLint ignore crcGoodE  "Use <$>"       -}
