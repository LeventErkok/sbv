-----------------------------------------------------------------------------
-- |
-- Module      :  Documentation.SBV.Examples.Misc.Enumerate
-- Copyright   :  (c) Brian Huffman
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Demonstrates how new sizes of word/int types can be defined and
-- used with SBV.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Documentation.SBV.Examples.Misc.Word4 where

import GHC.Enum (boundedEnumFrom, boundedEnumFromThen, toEnumError, succError, predError)

import Data.Bits
import Data.Generics (Data, Typeable)
import System.Random (Random(..))

import Data.SBV
import Data.SBV.Internals

-- | Word4 as a newtype. Invariant: @Word4 x@ should satisfy @x < 16@.
newtype Word4 = Word4 Word8
  deriving (Eq, Ord, Data, Typeable)

-- | Smart constructor; simplifies conversion from Word8
word4 :: Word8 -> Word4
word4 x = Word4 (x .&. 0x0f)

-- | Show instance
instance Show Word4 where
  show (Word4 x) = show x

-- | Read instance. We read as an 8-bit word, and coerce
instance Read Word4 where
  readsPrec p s = [ (word4 x, s') | (x, s') <- readsPrec p s ]

-- | Bounded instance; from 0 to 255
instance Bounded Word4 where
  minBound = Word4 0x00
  maxBound = Word4 0x0f

-- | Enum instance, trivial definitions.
instance Enum Word4 where
  succ (Word4 x) = if x < 0x0f then Word4 (succ x) else succError "Word4"
  pred (Word4 x) = if x > 0x00 then Word4 (pred x) else predError "Word4"
  toEnum i | 0x00 <= i && i <= 0x0f = Word4 (toEnum i)
           | otherwise              = toEnumError "Word4" i (Word4 0x00, Word4 0x0f)
  fromEnum (Word4 x) = fromEnum x
  -- Comprehensions
  enumFrom                                     = boundedEnumFrom
  enumFromThen                                 = boundedEnumFromThen
  enumFromTo     (Word4 x) (Word4 y)           = map Word4 (enumFromTo x y)
  enumFromThenTo (Word4 x) (Word4 y) (Word4 z) = map Word4 (enumFromThenTo x y z)

-- | Num instance, merely lifts underlying 8-bit operation and casts back
instance Num Word4 where
  Word4 x + Word4 y = word4 (x + y)
  Word4 x * Word4 y = word4 (x * y)
  Word4 x - Word4 y = word4 (x - y)
  negate (Word4 x)  = word4 (negate x)
  abs (Word4 x)     = Word4 x
  signum (Word4 x)  = Word4 (if x == 0 then 0 else 1)
  fromInteger n     = word4 (fromInteger n)

-- | Real instance simply uses the Word8 instance
instance Real Word4 where
  toRational (Word4 x) = toRational x

-- | Integral instance, again using Word8 instance and casting. NB. we do
-- not need to use the smart constructor here as neither the quotient nor
-- the remainder can overflow a Word4.
instance Integral Word4 where
  quotRem (Word4 x) (Word4 y) = (Word4 q, Word4 r)
    where (q, r) = quotRem x y
  toInteger (Word4 x) = toInteger x

-- | Bits instance
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
  bitSizeMaybe _        = Just 4
  isSigned _            = False
  testBit (Word4 x)     = testBit x
  bit i                 = word4 (bit i)
  popCount (Word4 x)    = popCount x

-- | Random instance, used in quick-check
instance Random Word4 where
  randomR (Word4 lo, Word4 hi) gen = (Word4 x, gen')
    where (x, gen') = randomR (lo, hi) gen
  random gen = (Word4 x, gen')
    where (x, gen') = randomR (0x00, 0x0f) gen

-- | SWord4 type synonym
type SWord4 = SBV Word4

-- | SymWord instance, allowing this type to be used in proofs/sat etc.
instance SymWord Word4 where
  mkSymWord  = genMkSymVar (KBounded False 4)
  literal    = genLiteral  (KBounded False 4)
  fromCW     = genFromCW

-- | HasKind instance; simply returning the underlying kind for the type
instance HasKind Word4 where
  kindOf _ = KBounded False 4

-- | SatModel instance, merely uses the generic parsing method.
instance SatModel Word4 where
  parseCWs = genParse (KBounded False 4)

-- | SDvisible instance, using 0-extension
instance SDivisible Word4 where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

-- | SDvisible instance, using default methods
instance SDivisible SWord4 where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

-- | SIntegral instance, using default methods
instance SIntegral Word4

-- | Joining/splitting to/from Word8
instance Splittable Word8 Word4 where
  split x           = (Word4 (x `shiftR` 4), word4 x)
  Word4 x # Word4 y = (x `shiftL` 4) .|. y
  extend (Word4 x)  = x
