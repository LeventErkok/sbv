-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Tools.Overflow
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Implementation of overflow detection functions.
-- Based on: <http://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/z3prefix.pdf>
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Data.SBV.Tools.Overflow (

         -- * Overflow detection
         BVOverflow(..)

    ) where

import Data.SBV.Core.Data
import Data.SBV.Dynamic

-- | Detecting underflow/overflow conditions. For each function,
-- the first result is the condition under which the computation
-- underflows, and the second is the condition under which it
-- overflows.
class BVOverflow a where
  -- | Bit-vector addition. Unsigned addition can only overflow. Signed addition can underflow and overflow.
  bvAddO :: a -> a -> (SBool, SBool)

  -- | Bit-vector subtraction. Unsigned subtraction can only underflow. Signed subtraction can underflow and overflow.
  bvSubO :: a -> a -> (SBool, SBool)

  -- | Bit-vector multiplication. Unsigned multiplication can only overflow. Signed multiplication can underflow and overflow.
  bvMulO :: a -> a -> (SBool, SBool)

  -- | Bit-vector division. Unsigned division neither underflows nor overflows. Signed division can only overflow.
  bvDivO :: a -> a -> (SBool, SBool)

  -- | Bit-vector negation. Unsigned negation neither underflows nor overflows. Signed negation can only overflow.
  bvNegO :: a -> (SBool, SBool)

instance BVOverflow SWord8  where {bvAddO = l2 bvAddO; bvSubO = l2 bvSubO; bvMulO = l2 bvMulO; bvDivO = l2 bvDivO; bvNegO = l1 bvNegO}
instance BVOverflow SWord16 where {bvAddO = l2 bvAddO; bvSubO = l2 bvSubO; bvMulO = l2 bvMulO; bvDivO = l2 bvDivO; bvNegO = l1 bvNegO}
instance BVOverflow SWord32 where {bvAddO = l2 bvAddO; bvSubO = l2 bvSubO; bvMulO = l2 bvMulO; bvDivO = l2 bvDivO; bvNegO = l1 bvNegO}
instance BVOverflow SWord64 where {bvAddO = l2 bvAddO; bvSubO = l2 bvSubO; bvMulO = l2 bvMulO; bvDivO = l2 bvDivO; bvNegO = l1 bvNegO}
instance BVOverflow SInt8   where {bvAddO = l2 bvAddO; bvSubO = l2 bvSubO; bvMulO = l2 bvMulO; bvDivO = l2 bvDivO; bvNegO = l1 bvNegO}
instance BVOverflow SInt16  where {bvAddO = l2 bvAddO; bvSubO = l2 bvSubO; bvMulO = l2 bvMulO; bvDivO = l2 bvDivO; bvNegO = l1 bvNegO}
instance BVOverflow SInt32  where {bvAddO = l2 bvAddO; bvSubO = l2 bvSubO; bvMulO = l2 bvMulO; bvDivO = l2 bvDivO; bvNegO = l1 bvNegO}
instance BVOverflow SInt64  where {bvAddO = l2 bvAddO; bvSubO = l2 bvSubO; bvMulO = l2 bvMulO; bvDivO = l2 bvDivO; bvNegO = l1 bvNegO}

instance BVOverflow SVal where
  bvAddO = signPick2 bvuaddo bvsaddo
  bvSubO = signPick2 bvusubo bvssubo
  bvMulO = signPick2 bvumulo bvsmulo
  bvDivO = signPick2 bvudivo bvsdivo
  bvNegO = signPick1 bvunego bvsnego

-- | Zero-extend to given bits
zx :: Int -> SVal -> SVal
zx n a
 | n < sa = error $ "Data.SBV: Unexpected zero extension: from: " ++ show (intSizeOf a) ++ " to: " ++ show n
 | True   = p `svJoin` a
 where sa = intSizeOf a
       s  = hasSign a
       p  = svInteger (KBounded s (n - sa)) 0

-- | Sign-extend to given bits. Note that we keep the signedness of the argument.
sx :: Int -> SVal -> SVal
sx n a
 | n < sa = error $ "Data.SBV: Unexpected sign extension: from: " ++ show (intSizeOf a) ++ " to: " ++ show n
 | True   = p `svJoin` a
 where sa = intSizeOf a
       mk = svInteger $ KBounded (hasSign a) (n - sa)
       p  = svIte (pos a) (mk 0) (mk (-1))

-- | Get the sign-bit
signBit :: SVal -> SVal
signBit x = x `svTestBit` (intSizeOf x - 1)

-- | Is the sign-bit high?
neg :: SVal -> SVal
neg x = signBit x `svEqual` svTrue

-- | Is the sign-bit low?
pos :: SVal -> SVal
pos x = signBit x `svEqual` svFalse

-- | Do these have the same sign?
sameSign :: SVal -> SVal -> SVal
sameSign x y = (pos x `svAnd` pos y) `svOr` (neg x `svAnd` neg y)

-- | Do these have opposing signs?
diffSign :: SVal -> SVal -> SVal
diffSign x y = svNot (sameSign x y)

-- | Check all true
svAll :: [SVal] -> SVal
svAll = foldr svAnd svTrue

-- | Unsigned addition. Can only overflow.
bvuaddo :: Int -> SVal -> SVal -> (SVal, SVal)
bvuaddo n x y = (underflow, overflow)
  where underflow = svFalse

        n'       = n+1
        overflow = neg $ zx n' x `svPlus` zx n' y

-- | Signed addition.
bvsaddo :: Int -> SVal -> SVal -> (SVal, SVal)
bvsaddo _n x y = (underflow, overflow)
  where underflow = svAll [neg x, neg y, pos (x `svPlus` y)]
        overflow  = svAll [pos x, pos y, neg (x `svPlus` y)]

-- | Unsigned subtraction. Can only underflow.
bvusubo :: Int -> SVal -> SVal -> (SVal, SVal)
bvusubo _n x y = (underflow, overflow)
  where underflow = y `svGreaterThan` x
        overflow  = svFalse

-- | Signed subtraction.
bvssubo :: Int -> SVal -> SVal -> (SVal, SVal)
bvssubo _n x y = (underflow, overflow)
  where underflow = svAll [neg x, pos y, pos (x `svMinus` y)]
        overflow  = svAll [pos x, neg y, neg (x `svMinus` y)]

-- | Unsigned multiplication. Can only overflow.
bvumulo :: Int -> SVal -> SVal -> (SVal, SVal)
bvumulo 0 _ _ = (svFalse,   svFalse)
bvumulo n x y = (underflow, overflow)
  where underflow = svFalse

        n'       = 2*n
        zn       = svInteger (KBounded False n) 0
        overflow = svNot $ svExtract (n'-1) n (zx n' x `svTimes` zx n' y) `svEqual` zn

-- | Signed multiplication.
bvsmulo :: Int -> SVal -> SVal -> (SVal, SVal)
bvsmulo 0 _ _ = (svFalse,   svFalse)
bvsmulo n x y = (underflow, overflow)
  where n'        = 2*n
        mul2n     = sx n' x `svTimes` sx n' y
        mul2nTop  = svExtract (n'-1) (n-1) mul2n

        zeros     = svInteger (KBounded True (n+1)) 0
        ones      = svInteger (KBounded True (n+1)) (-1)

        z         = svInteger (KBounded True n) 0
        noZeros   = svNot $ (x `svEqual` z) `svOr` (y `svEqual` z)

        underflow = svAll [noZeros, diffSign x y, svNot $ mul2nTop `svEqual` ones]
        overflow  = svAll [         sameSign x y, svNot $ mul2nTop `svEqual` zeros]

-- | Unsigned division. Neither underflows, nor overflows.
bvudivo :: Int -> SVal -> SVal -> (SVal, SVal)
bvudivo _ _ _ = (underflow, overflow)
  where underflow = svFalse
        overflow  = svFalse

-- | Signed division. Can only overflow.
bvsdivo :: Int -> SVal -> SVal -> (SVal, SVal)
bvsdivo n x y = (underflow, overflow)
  where underflow = svFalse

        ones      = svInteger (KBounded True n) (-1)
        topSet    = svInteger (KBounded True n) (2^(n-1))

        overflow = svAll [x `svEqual` topSet, y `svEqual` ones]

-- | Unsigned negation. Neither underflows, nor overflows.
bvunego :: Int -> SVal -> (SVal, SVal)
bvunego _ _ = (underflow, overflow)
  where underflow = svFalse
        overflow  = svFalse

-- | Signed negation. Can only overflow.
bvsnego :: Int -> SVal -> (SVal, SVal)
bvsnego n x = (underflow, overflow)
  where underflow = svFalse

        topSet    = svInteger (KBounded True n) (2^(n-1))
        overflow  = x `svEqual` topSet

-- Helpers
l2 :: (SVal -> SVal -> (SBool, SBool)) -> SBV a -> SBV a -> (SBool, SBool)
l2 f (SBV a) (SBV b) = f a b

l1 :: (SVal -> (SBool, SBool)) -> SBV a -> (SBool, SBool)
l1 f (SBV a) = f a

signPick2 :: (Int -> SVal -> SVal -> (SVal, SVal)) -> (Int -> SVal -> SVal -> (SVal, SVal)) -> (SVal -> SVal -> (SBool, SBool))
signPick2 fu fs a b
 | hasSign a = let (u, o) = fs n a b in (SBV u, SBV o)
 | True      = let (u, o) = fu n a b in (SBV u, SBV o)
 where n = intSizeOf a

signPick1 :: (Int -> SVal -> (SVal, SVal)) -> (Int -> SVal -> (SVal, SVal)) -> (SVal -> (SBool, SBool))
signPick1 fu fs a
 | hasSign a = let (u, o) = fs n a in (SBV u, SBV o)
 | True      = let (u, o) = fu n a in (SBV u, SBV o)
 where n = intSizeOf a
