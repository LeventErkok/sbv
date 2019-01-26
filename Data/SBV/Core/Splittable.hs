-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Core.Splittable
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Implementation of bit-vector concatanetation and splits
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}

module Data.SBV.Core.Splittable (Splittable(..)) where

import Data.Bits (Bits(..))
import Data.Word (Word8, Word16, Word32, Word64)

import Data.SBV.Core.Operations
import Data.SBV.Core.Data
import Data.SBV.Core.Model () -- instances only

infixr 5 #
-- | Splitting an @a@ into two @b@'s and joining back.
-- Intuitively, @a@ is a larger bit-size word than @b@, typically double.
-- The 'extend' operation captures embedding of a @b@ value into an @a@
-- without changing its semantic value.
class Splittable a b | b -> a where
  split  :: a -> (b, b)
  (#)    :: b -> b -> a
  extend :: b -> a

  {-# MINIMAL split, (#), extend #-}

genSplit :: (Integral a, Num b) => Int -> a -> (b, b)
genSplit ss x = (fromIntegral ((ix `shiftR` ss) .&. mask), fromIntegral (ix .&. mask))
  where ix = toInteger x
        mask = 2 ^ ss - 1

genJoin :: (Integral b, Num a) => Int -> b -> b -> a
genJoin ss x y = fromIntegral ((ix `shiftL` ss) .|. iy)
  where ix = toInteger x
        iy = toInteger y

-- concrete instances
instance Splittable Word64 Word32 where
  split = genSplit 32
  (#)   = genJoin  32
  extend b = 0 # b

instance Splittable Word32 Word16 where
  split = genSplit 16
  (#)   = genJoin  16
  extend b = 0 # b

instance Splittable Word16 Word8 where
  split = genSplit 8
  (#)   = genJoin  8
  extend b = 0 # b

-- symbolic instances
instance Splittable SWord64 SWord32 where
  split (SBV x) = (SBV (svExtract 63 32 x), SBV (svExtract 31 0 x))
  SBV a # SBV b = SBV (svJoin a b)
  extend b = 0 # b

instance Splittable SWord32 SWord16 where
  split (SBV x) = (SBV (svExtract 31 16 x), SBV (svExtract 15 0 x))
  SBV a # SBV b = SBV (svJoin a b)
  extend b = 0 # b

instance Splittable SWord16 SWord8 where
  split (SBV x) = (SBV (svExtract 15 8 x), SBV (svExtract 7 0 x))
  SBV a # SBV b = SBV (svJoin a b)
  extend b = 0 # b
