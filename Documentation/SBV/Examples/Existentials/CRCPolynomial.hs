-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Existentials.CRCPolynomial
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- This program demonstrates the use of the existentials and the QBVF (quantified
-- bit-vector solver). We generate CRC polynomials of degree 16 that can be used
-- for messages of size 48-bits. The query finds all such polynomials that have hamming
-- distance is at least 4. That is, if the CRC can't tell two different 48-bit messages
-- apart, then they must differ in at least 4 bits.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Existentials.CRCPolynomial where

import Data.SBV
import Data.SBV.Tools.Polynomial

-- | Compute the 16 bit CRC of a 48 bit message, using the given polynomial
crc_48_16 :: SWord 48 -> SWord16 -> [SBool]
crc_48_16 msg poly = crcBV 16 (blastBE msg) (blastBE poly)

-- | Count the differing bits in the message and the corresponding CRC
diffCount :: (SWord 48, [SBool]) -> (SWord 48, [SBool]) -> SWord8
diffCount (d1, crc1) (d2, crc2) = count xorBits
  where bits1   = blastBE d1 ++ crc1
        bits2   = blastBE d2 ++ crc2
        -- xor will give us a false if bits match, true if they differ
        xorBits = zipWith (.<+>) bits1 bits2
        count []     = 0
        count (b:bs) = let r = count bs in ite b (1+r) r

-- | Given a hamming distance value @hd@, 'crcGood' returns @true@ if
-- the 16 bit polynomial can distinguish all messages that has at most
-- @hd@ different bits. Note that we express this conversely: If the
-- @sent@ and @received@ messages are different, then it must be the
-- case that that must differ from each other (including CRCs), in
-- more than @hd@ bits.
crcGood :: SWord8 -> SWord16 -> SWord 48 -> SWord 48 -> SBool
crcGood hd poly sent received =
     sent ./= received .=> diffCount (sent, crcSent) (received, crcReceived) .>= hd
   where crcSent     = crc_48_16 sent     poly
         crcReceived = crc_48_16 received poly

-- | Generate good CRC polynomials for 48-bit words, given the hamming distance @hd@.
genPoly :: SWord8 -> Int -> IO ()
genPoly hd maxCnt = do res <- allSatWith defaultSMTCfg{allSatMaxModelCount = Just maxCnt} $ do
                                p <- sbvExists "polynomial" -- the polynomial is existentially specified
                                s <- sbvForall "sent"       -- sent word, universal
                                r <- sbvForall "received"   -- received word, universal
                                -- assert that the polynomial @p@ is good. Note
                                -- that we also supply the extra information that
                                -- the least significant bit must be set in the
                                -- polynomial, as all CRC polynomials have the "+1"
                                -- term in them set. This simplifies the query.
                                return $ sTestBit p 0 .&& crcGood hd p s r
                       cnt <- displayModels id disp res
                       putStrLn $ "Found: " ++ show cnt ++ " polynomail(s)."
        where disp :: Int -> (Bool, Word16) -> IO ()
              disp n (_, s) = putStrLn $ "Polynomial #" ++ show n ++ ". x^16 + " ++ showPolynomial False s

-- | Find and display all degree 16 polynomials with hamming distance at least 4, for 48 bit messages.
--
-- When run, this function prints:
--
--  @
--    Polynomial #1. x^16 + x^3 + x^2 + 1
--    Polynomial #2. x^16 + x^3 + x^2 + x + 1
--    Polynomial #3. x^16 + x^3 + x + 1
--    Polynomial #4. x^16 + x^15 + x^2 + 1
--    Polynomial #5. x^16 + x^15 + x^2 + x + 1
--    Found: 5 polynomial(s).
--  @
--
-- Note that different runs can produce different results, depending on the random
-- numbers used by the solver, solver version, etc. (Also, the solver will take some
-- time to generate these results. On my machine, the first five polynomials were
-- generated in about 5 minutes.)
findHD4Polynomials :: IO ()
findHD4Polynomials = genPoly 4 cnt
  where cnt = 5 -- Generate at most this many polynomials

{-# ANN crc_48_16 ("HLint: ignore Use camelCase" :: String) #-}
