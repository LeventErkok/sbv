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

module Data.SBV.BitVectors.PrettyNum (PrettyNum(..), readBin, shex, sbin) where

import Data.Char  (ord)
import Data.Int   (Int8, Int16, Int32, Int64)
import Data.List  (isPrefixOf)
import Data.Maybe (fromJust)
import Data.Word  (Word8, Word16, Word32, Word64)
import Numeric    (showIntAtBase, showHex, readInt)

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.Model () -- instances only

-- | PrettyNum class captures printing of numbers in hex and binary formats; also supporting negative numbers.
--
-- Minimal complete definition: 'hexS' and 'binS'
class PrettyNum a where
  -- | Show a number in hexadecimal (starting with @0x@)
  hexS :: a -> String
  -- | Show a number in binary (starting with @0b@)
  binS :: a -> String
  -- | IO version of 'hexS'
  hex :: a -> IO ()
  hex = putStrLn . hexS
  -- | IO version of 'binS'
  bin   :: a -> IO ()
  bin = putStrLn . binS

-- Why not default methods? Because defaults need "Integral a" but Bool is not..
instance PrettyNum Bool   where {hexS = show; binS = show}
instance PrettyNum Word8  where {hexS = shex True (False,8) ; binS = sbin True (False,8) }
instance PrettyNum Int8   where {hexS = shex True (True,8)  ; binS = sbin True (True,8)  }
instance PrettyNum Word16 where {hexS = shex True (False,16); binS = sbin True (False,16)}
instance PrettyNum Int16  where {hexS = shex True (True,16);  binS = sbin True (True,16) }
instance PrettyNum Word32 where {hexS = shex True (False,32); binS = sbin True (False,32)}
instance PrettyNum Int32  where {hexS = shex True (True,32);  binS = sbin True (True,32) }
instance PrettyNum Word64 where {hexS = shex True (False,64); binS = sbin True (False,64)}
instance PrettyNum Int64  where {hexS = shex True (True,64);  binS = sbin True (True,64) }

instance PrettyNum CW where
  hexS cw | cwIsBit cw  = hexS (cwToBool cw)
  hexS cw               = shex True (hasSign cw, sizeOf cw) (cwVal cw)

  binS cw | cwIsBit cw  = binS (cwToBool cw)
  binS cw               = sbin True (hasSign cw, sizeOf cw) (cwVal cw)

instance (SymWord a, PrettyNum a) => PrettyNum (SBV a) where
  hexS s = maybe (show s) (hexS :: a -> String) $ unliteral s
  binS s = maybe (show s) (binS :: a -> String) $ unliteral s

shex :: (Integral a) => Bool -> (Bool, Size) -> a -> String
shex shType (signed, size) a
 | a < 0
 = "-0x" ++ pad l (s16 (abs ((fromIntegral a) :: Integer)))  ++ t
 | True
 =  "0x" ++ pad l (s16 a) ++ t
 where t | shType = " :: " ++ (if signed then "Int" else "Word") ++ show size
         | True   = ""
       l = (size + 3) `div` 4

sbin :: (Integral a) => Bool -> (Bool, Size) -> a -> String
sbin shType (signed,size) a
 | a < 0
 = "-0b" ++ pad size (s2 (abs ((fromIntegral a) :: Integer)))  ++ t
 | True
 =  "0b" ++ pad size (s2 a) ++ t
 where t | shType = " :: " ++ (if signed then "Int" else "Word") ++ show size
         | True   = ""

pad :: Int -> String -> String
pad l s = replicate (l - length s) '0' ++ s

s2, s16 :: Integral a => a -> String
s2  v = showIntAtBase 2 dig v "" where dig = fromJust . flip lookup [(0, '0'), (1, '1')]
s16 v = showHex v ""

-- | A more convenient interface for reading binary numbers, also supports negative numbers
readBin :: Num a => String -> a
readBin ('-':s) = -(readBin s)
readBin s = case readInt 2 isDigit cvt s' of
              [(a, "")] -> a
              _         -> error $ "SBV.readBin: Cannot read a binary number from: " ++ show s
  where cvt c = ord c - ord '0'
        isDigit = (`elem` "01")
        s' | "0b" `isPrefixOf` s = drop 2 s
           | True                = s
