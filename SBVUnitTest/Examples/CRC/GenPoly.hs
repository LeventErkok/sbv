-----------------------------------------------------------------------------
-- |
-- Module      :  Examples.CRC.GenPoly
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Finds good polynomials for CRC's
-----------------------------------------------------------------------------

module Examples.CRC.GenPoly where

import Data.SBV

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
     sent ./= received ==> diffCount frameSent frameReceived .> hd
   where frameSent     = mkFrame poly sent
         frameReceived = mkFrame poly received
         poly          = mkPoly divisor

mkPoly :: SWord16 -> SWord64
mkPoly d = 0 # 1 # d

-- how long do we wait for each poly.. (seconds)
waitFor :: Int
waitFor = 15

genPoly :: SWord8 -> IO ()
genPoly hd = do putStrLn $ "*** Looking for polynomials with HD = " ++ show hd
                (skipped, res) <- go 0 [] []
                putStrLn $ "*** Good polynomials with HD = " ++ show hd
                mapM_ (\(i, s) -> putStrLn (show i ++ ". " ++ showPoly (mkPoly s)))  (zip [(1::Integer)..] res)
                putStrLn $ "*** Skipped the followings, proof exceeded timeout value of " ++ show waitFor
                mapM_ (\(i, s) -> putStrLn (show i ++ ". " ++ showPoly (mkPoly s)))  (zip [(1::Integer)..] skipped)
                putStrLn "*** Done."
  where go :: SWord16 -> [SWord16] -> [SWord16] -> IO ([SWord16], [SWord16])
        go poly skip acc
         | poly == maxBound = return (skip, acc)
         | True             = do putStr $ "Testing " ++ showPoly  (mkPoly poly) ++ "... "
                                 thm <- isTheorem (Just waitFor) $ crcGood hd poly
                                 case thm of
                                   Nothing    -> do putStrLn "Timeout, skipping.."
                                                    go (poly+1) (poly:skip) acc
                                   Just True  -> do putStrLn "Good!"
                                                    go (poly+1) skip (poly:acc)
                                   Just False -> do putStrLn "Bad!"
                                                    go (poly+1) skip acc

findHD3Polynomials :: IO ()
findHD3Polynomials = genPoly 3

{-# ANN crc_48_16 ("HLint: ignore Use camelCase" :: String) #-}
