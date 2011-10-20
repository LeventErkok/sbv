-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.SignCast
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Implementation of casting between signed/unsigned variants of the
-- same type.
-----------------------------------------------------------------------------

{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE PatternGuards          #-}
{-# LANGUAGE FlexibleInstances      #-}

module Data.SBV.BitVectors.SignCast (SignCast(..)) where

import Data.Word (Word8, Word16, Word32, Word64)
import Data.Int  (Int8,  Int16,  Int32,  Int64)

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.Model()  -- instances only

-- | Sign casting a value into another. This essentially
-- means forgetting the sign bit and reinterpreting the bits
-- accordingly when converting a signed value to an unsigned
-- one. Similarly, when an unsigned quantity is converted to
-- a signed one, the most significant bit is interpreted
-- as the sign. We only define instances when the source
-- and target types are precisely the same size.
-- The idea is that 'signCast' and 'unsignCast' must form
-- an isomorphism pair between the types @a@ and @b@, i.e., we
-- expect the following two properties to hold:
--
-- @
--    signCast . unsignCast = id
--    unsingCast . signCast = id
-- @
--
-- Note that one naive way to implement both these operations
-- is simply to compute @fromBitsLE . blastLE@, i.e., first
-- get all the bits of the word and then reconstruct in the target
-- type. While this is semantically correct, it generates a lot
-- of code (both during proofs via SMT-Lib, and when compiled to C).
-- The goal of this class is to avoid that cost, so these operations
-- can be compiled very efficiently, they will essentially become no-op's.
--
-- Minimal complete definition: All, no defaults.
class SignCast a b | a -> b, b -> a where
  -- | Interpret as a signed word
  signCast   :: a -> b
  -- | Interpret as an unsigned word
  unsignCast :: b -> a

-- concrete instances
instance SignCast Word64 Int64 where
  signCast   = fromIntegral
  unsignCast = fromIntegral

instance SignCast Word32 Int32 where
  signCast   = fromIntegral
  unsignCast = fromIntegral

instance SignCast Word16 Int16 where
  signCast   = fromIntegral
  unsignCast = fromIntegral

instance SignCast Word8  Int8  where
  signCast   = fromIntegral
  unsignCast = fromIntegral

-- A generic implementation can be along the following lines:
--      fromBitsLE . blastLE
-- However, we prefer this version as the above will generate
-- a ton more code during compilation to SMT-Lib and C
genericSign :: (Integral a, SymWord a, Num b, SymWord b) => SBV a -> SBV b
genericSign x
  | Just c <- unliteral x = literal $ fromIntegral c
  | True                  = SBV sgsz (Right (cache y))
     where sgsz@(_, sz) = (True, sizeOf x)
           y st = do xsw <- sbvToSW st x
                     newExpr st sgsz (SBVApp (Extract (sz-1) 0) [xsw])

-- Same comments as above, regarding the implementation.
genericUnsign :: (Integral a, SymWord a, Num b, SymWord b) => SBV a -> SBV b
genericUnsign x
  | Just c <- unliteral x = literal $ fromIntegral c
  | True                  = SBV sgsz (Right (cache y))
     where sgsz@(_, sz) = (False, sizeOf x)
           y st = do xsw <- sbvToSW st x
                     newExpr st sgsz (SBVApp (Extract (sz-1) 0) [xsw])

-- symbolic instances
instance SignCast SWord8 SInt8 where
  signCast   = genericSign
  unsignCast = genericUnsign

instance SignCast SWord16 SInt16 where
  signCast   = genericSign
  unsignCast = genericUnsign

instance SignCast SWord32 SInt32 where
  signCast   = genericSign
  unsignCast = genericUnsign

instance SignCast SWord64 SInt64 where
  signCast   = genericSign
  unsignCast = genericUnsign
