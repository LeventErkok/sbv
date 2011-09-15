-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.CRC.CCITT
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- CRC checks, hamming distance, etc.
-----------------------------------------------------------------------------

module Data.SBV.Examples.CRC.CCITT where

import Data.SBV

-- We don't have native support for 48 bits in Data.SBV
-- So, represent as 32 high-bits and 16 low
type SWord48 = (SWord32, SWord16)

extendData :: SWord48 -> SWord64
extendData (h, l) = h # l # 0

mkFrame :: SWord48 -> SWord64
mkFrame msg@(h, l) = h # l # crc msg

crc :: SWord48 -> SWord16
crc msg = res
  where msg64, divisor :: SWord64
        msg64   = extendData msg
        divisor = polynomial [16, 12, 5, 0]
        crc64 = pMod msg64 divisor
        (_, res) = split (snd (split crc64))

diffCount :: SWord64 -> SWord64 -> SWord8
diffCount x y = count $ zipWith (.==) (blastLE x) (blastLE y)
  where count []     = 0
        count (b:bs) = let r = count bs in ite b r (1+r)

-- Claim: If there is an undetected corruption, it must be at least at 4 bits; i.e. HD is 3
crcGood :: SWord48 -> SWord48 -> SBool
crcGood sent received =
     sent ./= received ==> diffCount frameSent frameReceived .> 3
   where frameSent     = mkFrame sent
         frameReceived = mkFrame received

-- How come we get way more than 168 (= 2*84) counter-examples for this? 
hw4has84Inhabitants :: SWord48 -> SWord48 -> SBool
hw4has84Inhabitants sent received = fourBitError
   where frameSent     = mkFrame sent
         frameReceived = mkFrame received
         fourBitError  = diffCount frameSent frameReceived .== 4

hw4 :: IO ()
hw4 = do res <- allSat hw4has84Inhabitants
         cnt <- displayModels disp res
         putStrLn $ "Found: " ++ show cnt ++ " solution(s)."
   where disp :: Int -> (Word32, Word16, Word32, Word16) -> IO ()
         disp i (sh, sl, rh, rl) = do putStrLn $ "Solution #" ++ show i ++ ": "
                                      putStrLn $ "  Sent    : " ++ binS (mkFrame (literal sh, literal sl))
                                      putStrLn $ "  Received: " ++ binS (mkFrame (literal rh, literal rl))
