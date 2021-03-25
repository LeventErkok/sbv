-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.CrackNum
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Utilities for cracking numbers in detail
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.CrackNum(encode, decode) where

import Data.Char
import Data.List
import Data.SBV
import Data.SBV.Control
import GHC.TypeLits
import Numeric

-- | A class of types with an explicit memory layout, such as
-- IEEE754 floats, or machine words and integers.
class SymVal a => BitLayout a where
  -- | Big endian blasting of the value into bits
  blast :: SBV a -> [SBool]

  -- | Encoding the value into the memory layout
  encode :: a -> IO SatResult
  encode v = satWith z3{crackNum=True} $ do
                x <- free "ENCODED"
                pure $ x .=== literal v

  -- | Decoding a memory layout represented as a binary ro hex-string
  decode :: String -> IO (a, SatResult)
  decode input = runSMTWith z3{crackNum=True} $ do
                    x <- free "DECODED"
                    constrain $ match (blast x) $ map literal (concat [cvt c | c <- bitString, not (isSkippable c)])
                    query $ do ensureSat
                               xv <- getValue x
                               constrain $ x .=== literal xv
                               ensureSat
                               m <- getSMTResult
                               pure (xv, SatResult m)
      where match []     []     = sTrue
            match []     rest   = error $ "Input has too many digits. Extras: " ++ show rest
            match rest   []     = error $ "Input has too few digits. It needs " ++ show (length rest) ++ " more."
            match (x:xs) (y:ys) = x .== y .&& match xs ys

            cvt | isHex = cvtHex
                | True  = cvtBin

            isHex
              | "0x" `isPrefixOf` input = True
              | "0b" `isPrefixOf` input = False
              | True                    = error "Input string must start with 0b or 0x"

            bitString = drop 2 input

            cvtBin :: Char -> [Bool]
            cvtBin '1' = [True]
            cvtBin '0' = [False]
            cvtBin c   = error $ "Input has a non-binary digit: " ++ show c

            cvtHex :: Char -> [Bool]
            cvtHex c = case readHex [c] of
                         [(v, "")] -> pad $ concatMap cvtBin $ reverse $ map intToDigit $ unfoldr (\x -> if x == 0 then Nothing else Just (x `rem` 2, x `div` 2)) v
                         _         -> error $ "Input has a non-hexadecimal digit: " ++ show c
              where pad p = replicate (4 - length p) False ++ p

            isSkippable c = c `elem` "_-" || isSpace c

-- | Unsigned words as values that can be laid out.
instance (KnownNat n, BVIsNonZero n) => BitLayout (WordN n) where
  blast = blastBE

-- | Signed integers as values that can be laid out.
instance (KnownNat n, BVIsNonZero n) => BitLayout (IntN n) where
  blast = blastBE

-- | IEEE-754 double-precison floats that can be laid out.
instance BitLayout Double where
  blast x = s : e ++ m where (s, e, m) = blastSDouble x

-- | IEEE-754 single-precison floats that can be laid out.
instance BitLayout Float where
  blast x = s : e ++ m where (s, e, m) = blastSFloat x

-- | IEEE-754 arbitrary-precison floats that can be laid out.
instance (ValidFloat eb sb, KnownNat (eb + sb), BVIsNonZero (eb + sb)) => BitLayout (FloatingPoint eb sb) where
  blast x = s : e ++ m where (s, e, m) = blastSFloatingPoint x
