-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.PrettyNum
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Number representations in hex/bin
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE PatternGuards #-}

module Data.SBV.BitVectors.PrettyNum (hex, hexS, bin, binS, readBin) where

import Data.Maybe(fromJust)
import Data.Char(ord)
import Data.List(isPrefixOf)
import Data.Int
import Data.Word
import Numeric

import Data.SBV.BitVectors.Bit
import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.Model () -- instances only

class PrettyNum a where
  hexS, binS :: a -> String
  hex, bin   :: a -> IO ()
  hex = putStrLn . hexS
  bin = putStrLn . binS

-- Why not default methods? Because defaults need "Integral a" and Bool/Bit are not..
instance PrettyNum Bool   where {hexS = show; binS = show}
instance PrettyNum Bit    where {hexS = show; binS = show}
instance PrettyNum Word8  where {hexS = shex; binS = sbin}
instance PrettyNum Int8   where {hexS = shex; binS = sbin}
instance PrettyNum Word16 where {hexS = shex; binS = sbin}
instance PrettyNum Int16  where {hexS = shex; binS = sbin}
instance PrettyNum Word32 where {hexS = shex; binS = sbin}
instance PrettyNum Int32  where {hexS = shex; binS = sbin}
instance PrettyNum Word64 where {hexS = shex; binS = sbin}
instance PrettyNum Int64  where {hexS = shex; binS = sbin}

instance PrettyNum CW where
  hexS (W1  i) = hexS $ bit2Bool i
  hexS (W8  i) = hexS i
  hexS (W16 i) = hexS i
  hexS (W32 i) = hexS i
  hexS (W64 i) = hexS i
  hexS (I8  i) = hexS i
  hexS (I16 i) = hexS i
  hexS (I32 i) = hexS i
  hexS (I64 i) = hexS i
  binS (W1  i) = binS $ bit2Bool i
  binS (W8  i) = binS i
  binS (W16 i) = binS i
  binS (W32 i) = binS i
  binS (W64 i) = binS i
  binS (I8  i) = binS i
  binS (I16 i) = binS i
  binS (I32 i) = binS i
  binS (I64 i) = binS i

instance (SymWord a, PrettyNum a) => PrettyNum (SBV a) where
  hexS s = maybe (show s) (hexS :: a -> String) $ unliteral s
  binS s = maybe (show s) (binS :: a -> String) $ unliteral s

shex :: (HasSignAndSize a, Integral a) => a -> String
shex a
 | a < 0
 = "-0x" ++ pad l (s16 (abs ((fromIntegral a) :: Integer)))  ++ t
 | True
 =  "0x" ++ pad l (s16 a) ++ t
 where t = " :: [" ++ show (l*4) ++ (if hasSign a then "S" else "U") ++ "]"
       l = sizeOf a `div` 4

sbin :: (HasSignAndSize a, Integral a) => a -> String
sbin a
 | a < 0
 = "-0b" ++ pad l (s2 (abs ((fromIntegral a) :: Integer)))  ++ t
 | True
 =  "0b" ++ pad l (s2 a) ++ t
 where t = " :: [" ++ show l ++ (if hasSign a then "S" else "U") ++ "]"
       l = sizeOf a

pad :: Int -> String -> String
pad l s = replicate (l - length s) '0' ++ s

s2, s16 :: Integral a => a -> String
s2  v = showIntAtBase 2 dig v "" where dig = fromJust . flip lookup [(0, '0'), (1, '1')]
s16 v = showHex v ""

-- a more convenient interface for reading binary numbers
-- also supporting negatives
readBin :: Num a => String -> a
readBin ('-':s) = -(readBin s)
readBin s = case readInt 2 isDigit cvt s' of
              [(a, "")] -> a
              _         -> error $ "SBV.readBin: Cannot read a binary number from: " ++ show s
  where cvt c = ord c - ord '0'
        isDigit = (`elem` "01")
        s' | "0b" `isPrefixOf` s = drop 2 s
           | True                = s
