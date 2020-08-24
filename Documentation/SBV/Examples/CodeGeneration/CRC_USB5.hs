-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.CodeGeneration.CRC_USB5
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Computing the CRC symbolically, using the USB polynomial. We also
-- generating C code for it as well. This example demonstrates the
-- use of the 'crcBV' function, along with how CRC's can be computed
-- mathematically using polynomial division. While the results are the
-- same (i.e., proven equivalent, see 'crcGood' below), the internal
-- CRC implementation generates much better code, compare 'cg1' vs 'cg2' below.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.CodeGeneration.CRC_USB5 where

import Data.SBV
import Data.SBV.Tools.CodeGen
import Data.SBV.Tools.Polynomial

-----------------------------------------------------------------------------
-- * The USB polynomial
-----------------------------------------------------------------------------

-- | The USB CRC polynomial: @x^5 + x^2 + 1@.
-- Although this polynomial needs just 6 bits to represent (5 if higher
-- order bit is implicitly assumed to be set), we'll simply use a 16 bit
-- number for its representation to keep things simple for code generation
-- purposes.
usb5 :: SWord16
usb5 = polynomial [5, 2, 0]

-----------------------------------------------------------------------------
-- * Computing CRCs
-----------------------------------------------------------------------------

-- | Given an 11 bit message, compute the CRC of it using the USB polynomial,
-- which is 5 bits, and then append it to the msg to get a 16-bit word. Again,
-- the incoming 11-bits is represented as a 16-bit word, with 5 highest bits
-- essentially ignored for input purposes.
crcUSB :: SWord16 -> SWord16
crcUSB i = fromBitsBE (ib ++ cb)
  where ib = drop 5  (blastBE i)    -- only the last 11 bits needed
        pb = drop 11 (blastBE usb5) -- only the last  5 bits needed
        cb = crcBV 5 ib pb

-- | Alternate method for computing the CRC, /mathematically/. We shift
-- the number to the left by 5, and then compute the remainder from the
-- polynomial division by the USB polynomial. The result is then appended
-- to the end of the message.
crcUSB' :: SWord16 -> SWord16
crcUSB' i' = i .|. pMod i usb5
  where i = i' `shiftL` 5

-----------------------------------------------------------------------------
-- * Correctness
-----------------------------------------------------------------------------

-- | Prove that the custom 'crcBV' function is equivalent to the mathematical
-- definition of CRC's for 11 bit messages. We have:
--
-- >>> crcGood
-- Q.E.D.
crcGood :: IO ThmResult
crcGood = prove $ \i -> crcUSB i .== crcUSB' i

-----------------------------------------------------------------------------
-- * Code generation
-----------------------------------------------------------------------------

-- | Generate a C function to compute the USB CRC, using the internal CRC
-- function.
cg1 :: IO ()
cg1 = compileToC (Just "crcUSB1") "crcUSB1" $ do
        msg <- cgInput "msg"
        cgOutput "crc" (crcUSB msg)

-- | Generate a C function to compute the USB CRC, using the mathematical
-- definition of the CRCs. While this version generates functionally equivalent
-- C code, it's less efficient; it has about 30% more code. So, the above
-- version is preferable for code generation purposes.
cg2 :: IO ()
cg2 = compileToC (Just "crcUSB2") "crcUSB2" $ do
        msg <- cgInput "msg"
        cgOutput "crc" (crcUSB' msg)
