-- Demonstrates how new sizes of word/int types can be defined and
-- used with SBV.

{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Data.SBV.Examples.Misc.Word4 where

import GHC.Enum (boundedEnumFrom, boundedEnumFromThen, toEnumError, succError, predError)

import Data.Bits
import Data.Word (Word8)
import Data.Generics (Data, Typeable)
import System.Random (Random(..))

import Data.SBV
import Data.SBV.Internals

-- | Word4 as a newtype. Invariant: @Word4 x@ should satisfy @x < 16@.
newtype Word4 = Word4 Word8
  deriving (Eq, Ord, Data, Typeable)

-- | Smart constructor
word4 :: Word8 -> Word4
word4 x = Word4 (x .&. 0x0f)

instance Show Word4 where
  show (Word4 x) = show x

instance Read Word4 where
  readsPrec p s = [ (word4 x, s') | (x, s') <- readsPrec p s ]

instance Bounded Word4 where
  minBound = Word4 0x00
  maxBound = Word4 0x0f

instance Enum Word4 where
  succ (Word4 x) = if x < 0x0f then Word4 (succ x) else succError "Word4"
  pred (Word4 x) = if x > 0x00 then Word4 (pred x) else predError "Word4"
  toEnum i | 0x00 <= i && i <= 0x0f = Word4 (toEnum i)
           | otherwise              = toEnumError "Word4" i (Word4 0x00, Word4 0x0f)
  fromEnum (Word4 x) = fromEnum x
  enumFrom = boundedEnumFrom
  enumFromThen = boundedEnumFromThen
  enumFromTo (Word4 x) (Word4 y) = map Word4 (enumFromTo x y)
  enumFromThenTo (Word4 x) (Word4 y) (Word4 z) = map Word4 (enumFromThenTo x y z)

instance Num Word4 where
  Word4 x + Word4 y = word4 (x + y)
  Word4 x * Word4 y = word4 (x * y)
  Word4 x - Word4 y = word4 (x - y)
  negate (Word4 x)  = word4 (negate x)
  abs (Word4 x)     = Word4 x
  signum (Word4 x)  = Word4 (if x == 0 then 0 else 1)
  fromInteger n     = word4 (fromInteger n)

instance Real Word4 where
  toRational (Word4 x) = toRational x

instance Integral Word4 where
  quotRem (Word4 x) (Word4 y) = (Word4 q, Word4 r)
    where (q, r) = quotRem x y
  toInteger (Word4 x) = toInteger x

instance Bits Word4 where
  Word4 x  .&.  Word4 y = Word4 (x  .&.  y)
  Word4 x  .|.  Word4 y = Word4 (x  .|.  y)
  Word4 x `xor` Word4 y = Word4 (x `xor` y)
  complement (Word4 x)  = Word4 (x `xor` 0x0f)
  Word4 x `shift`  i    = word4 (shift x i)
  Word4 x `shiftL` i    = word4 (shiftL x i)
  Word4 x `shiftR` i    = Word4 (shiftR x i)
  Word4 x `rotate` i    = word4 (x `shiftL` k .|. x `shiftR` (4-k))
                            where k = i .&. 3
  bitSize _             = 4
#if __GLASGOW_HASKELL__ >= 708
  bitSizeMaybe _        = Just 4
#endif
  isSigned _            = False
  testBit (Word4 x) i   = testBit x i
  bit i                 = word4 (bit i)
  popCount (Word4 x)    = popCount x

instance Random Word4 where
  randomR (Word4 lo, Word4 hi) gen = (Word4 x, gen')
    where (x, gen') = randomR (lo, hi) gen
  random gen = (Word4 x, gen')
    where (x, gen') = randomR (0x00, 0x0f) gen


-- | SWord4 type synonym
type SWord4 = SBV Word4

instance SymWord Word4 where
  mkSymWord  = genMkSymVar (KBounded False 4)
  literal    = genLiteral  (KBounded False 4)
  fromCW     = genFromCW
  mbMaxBound = Just maxBound
  mbMinBound = Just minBound

instance HasKind Word4 where
  kindOf _ = KBounded False 4

instance SatModel Word4 where
  parseCWs = genParse (KBounded False 4)

instance SDivisible Word4 where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

instance SDivisible SWord4 where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

instance SIntegral Word4

instance FromBits SWord4 where
  fromBitsLE = checkAndConvert 4

instance Splittable Word8 Word4 where
  split x = (Word4 (x `shiftR` 4), word4 x)
  Word4 x # Word4 y = (x `shiftL` 4) .|. y
  extend (Word4 x) = x
