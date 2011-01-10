-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.Splittable
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Implementation of bit-vector concatanetation and splits
-----------------------------------------------------------------------------

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}

module Data.SBV.BitVectors.Splittable (FromBits(..), split, (#), extend) where

import Data.Word

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.Model

infixr 5 #
class Splittable a b | b -> a where
  split  :: a -> (b, b)
  (#)    :: b -> b -> a
  extend :: b -> a

genSplit :: (Integral a, Num b) => Int -> Integer -> a -> (b, b)
genSplit ss mask x = (fromIntegral ((ix `shiftR` ss) .&. mask), fromIntegral (ix .&. mask))
  where ix = toInteger x

genJoin :: (Integral b, Num a) => Int -> b -> b -> a
genJoin ss x y = fromIntegral ((ix `shiftL` ss) .|. iy)
  where ix = toInteger x
        iy = toInteger y

-- concrete instances
instance Splittable Word64 Word32 where
  split = genSplit 32 4294967295
  (#)   = genJoin  32
  extend b = 0 # b

instance Splittable Word32 Word16 where
  split = genSplit 16 65535
  (#)   = genJoin  16
  extend b = 0 # b

instance Splittable Word16 Word8 where
  split = genSplit 8 255
  (#)   = genJoin  8
  extend b = 0 # b

-- symbolic instances
instance Splittable SWord64 SWord32 where
  split (SBV _ (Left (W64 z))) = (literal x, literal y) where (x, y) = split z
  split z                      = (SBV (False, 32) (Right (cache x)), SBV (False, 32) (Right (cache y)))
    where x st = do zsw <- sbvToSW st z
                    newExpr st (False, 32) (SBVApp (Extract 63 32) [zsw])
          y st = do zsw <- sbvToSW st z
                    newExpr st (False, 32) (SBVApp (Extract 31  0) [zsw])
  (SBV _ (Left (W32 a))) # (SBV _ (Left (W32 b))) = SBV (False, 64) (Left (W64 (a # b)))
  a # b = SBV (False, 64) (Right (cache c))
    where c st = do asw <- sbvToSW st a
                    bsw <- sbvToSW st b
                    newExpr st (False, 64) (SBVApp Join [asw, bsw])
  extend b = 0 # b

instance Splittable SWord32 SWord16 where
  split (SBV _ (Left (W32 z))) = (literal x, literal y) where (x, y) = split z
  split z                      = (SBV (False, 16) (Right (cache x)), SBV (False, 16) (Right (cache y)))
    where x st = do zsw <- sbvToSW st z
                    newExpr st (False, 16) (SBVApp (Extract 31 16) [zsw])
          y st = do zsw <- sbvToSW st z
                    newExpr st (False, 16) (SBVApp (Extract 15  0) [zsw])
  (SBV _ (Left (W16 a))) # (SBV _ (Left (W16 b))) = SBV (False, 32) (Left (W32 (a # b)))
  a # b = SBV (False, 32) (Right (cache c))
    where c st = do asw <- sbvToSW st a
                    bsw <- sbvToSW st b
                    newExpr st (False, 32) (SBVApp Join [asw, bsw])
  extend b = 0 # b

instance Splittable SWord16 SWord8 where
  split (SBV _ (Left (W16 z))) = (literal x, literal y) where (x, y) = split z
  split z                      = (SBV (False, 8) (Right (cache x)), SBV (False, 8) (Right (cache y)))
    where x st = do zsw <- sbvToSW st z
                    newExpr st (False, 8) (SBVApp (Extract 15 8) [zsw])
          y st = do zsw <- sbvToSW st z
                    newExpr st (False, 8) (SBVApp (Extract  7 0) [zsw])
  (SBV _ (Left (W8 a))) # (SBV _ (Left (W8 b))) = SBV (False, 16) (Left (W16 (a # b)))
  a # b = SBV (False, 16) (Right (cache c))
    where c st = do asw <- sbvToSW st a
                    bsw <- sbvToSW st b
                    newExpr st (False, 16) (SBVApp Join [asw, bsw])
  extend b = 0 # b

-- unblasting
class FromBits a where
 fromBitsLE, fromBitsBE :: [SBool] -> a
 -- for a signed number in little-endian, we assume the very last bit is the sign digit
 -- this sounds weird a bit, but it is more consistent with the "reverse" view of
 -- LE/BE representations
 fromBitsBE = fromBitsLE . reverse

fromBinLE :: (Bits a, SymWord a) => [SBool] -> SBV a
fromBinLE = go 0 0
  where go !acc _  []     = acc
        go !acc !i (x:xs) = go (ite x (setBit acc i) acc) (i+1) xs

-- little-endian input
checkAndConvert :: (Bits a, SymWord a) => Int -> [SBool] -> SBV a
checkAndConvert sz xs
  | sz /= l
  = error $ "SBV.fromBits.SWord" ++ ssz ++ ": Expected " ++ ssz ++ " elements, got: " ++ show l
  | True
  = fromBinLE xs
  where l   = length xs
        ssz = show sz

-- little-endian input
checkAndConvertSigned :: (Bits a, SymWord a) => Int -> [SBool] -> SBV a
checkAndConvertSigned sz xs
  | sz /= l
  = error $ "SBV.fromBits.SInt" ++ ssz ++ ": Expected " ++ ssz ++ " elements, got: " ++ show l
  | True
  = ite sgn (-res) res
  where l   = length xs
        ssz = show sz
        sgn = last xs
        res = fromBinLE (init xs)

instance FromBits SBool where
 fromBitsLE [x] = x
 fromBitsLE xs  = error $ "SBV.fromBits.SBool: Expected 1 element, got: " ++ show (length xs)

instance FromBits SWord8  where fromBitsLE = checkAndConvert        8
instance FromBits SInt8   where fromBitsLE = checkAndConvertSigned  8
instance FromBits SWord16 where fromBitsLE = checkAndConvert       16
instance FromBits SInt16  where fromBitsLE = checkAndConvertSigned 16
instance FromBits SWord32 where fromBitsLE = checkAndConvert       32
instance FromBits SInt32  where fromBitsLE = checkAndConvertSigned 32
instance FromBits SWord64 where fromBitsLE = checkAndConvert       64
instance FromBits SInt64  where fromBitsLE = checkAndConvertSigned 64
