-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Core.Sized
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Type-level sized bit-vectors. Thanks to Ben Blaxill for providing an
-- initial implementation of this idea.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Core.Sized (
        -- * Type-sized unsigned bit-vectors
          WordN
        -- * Type-sized signed bit-vectors
        , IntN
       ) where

import Data.Bits
import Data.Maybe (fromJust)
import Data.Proxy (Proxy(..))

import GHC.TypeLits
import GHC.Real

import Data.SBV.Core.Kind
import Data.SBV.Core.Symbolic
import Data.SBV.Core.Concrete
import Data.SBV.Core.Operations

import Test.QuickCheck(Arbitrary(..))

-- | An unsigned bit-vector carrying its size info
newtype WordN (n :: Nat) = WordN Integer deriving (Eq, Ord)

-- | Show instance for t'WordN'
instance Show (WordN n) where
  show (WordN v) = show v

-- | t'WordN' has a kind
instance (KnownNat n, BVIsNonZero n) => HasKind (WordN n) where
  kindOf _ = KBounded False (intOfProxy (Proxy @n))

-- | A signed bit-vector carrying its size info
newtype IntN (n :: Nat) = IntN Integer deriving (Eq, Ord)

-- | Show instance for t'IntN'
instance Show (IntN n) where
  show (IntN v) = show v

-- | t'IntN' has a kind
instance (KnownNat n, BVIsNonZero n) => HasKind (IntN n) where
  kindOf _ = KBounded True (intOfProxy (Proxy @n))

-- Lift a unary operation via SVal
lift1 :: (KnownNat n, BVIsNonZero n, HasKind (bv n), Integral (bv n), Show (bv n)) => String -> (SVal -> SVal) -> bv n -> bv n
lift1 nm op x = uc $ op (c x)
  where k = kindOf x
        c = SVal k . Left . normCV . CV k . CInteger . toInteger
        uc (SVal _ (Left (CV _ (CInteger v)))) = fromInteger v
        uc r                                   = error $ "Impossible happened while lifting " ++ show nm ++ " over " ++ show (k, x, r)

-- Lift a binary operation via SVal
lift2 :: (KnownNat n, BVIsNonZero n, HasKind (bv n), Integral (bv n), Show (bv n)) => String -> (SVal -> SVal -> SVal) -> bv n -> bv n -> bv n
lift2 nm op x y = uc $ c x `op` c y
  where k = kindOf x
        c = SVal k . Left . normCV . CV k . CInteger . toInteger
        uc (SVal _ (Left (CV _ (CInteger v)))) = fromInteger v
        uc r                                   = error $ "Impossible happened while lifting " ++ show nm ++ " over " ++ show (k, x, y, r)

-- Lift a binary operation via SVal where second argument is an Int
lift2I :: (KnownNat n, BVIsNonZero n, HasKind (bv n), Integral (bv n), Show (bv n)) => String -> (SVal -> Int -> SVal) -> bv n -> Int -> bv n
lift2I nm op x i = uc $ c x `op` i
  where k = kindOf x
        c = SVal k . Left . normCV . CV k . CInteger . toInteger
        uc (SVal _ (Left (CV _ (CInteger v)))) = fromInteger v
        uc r                                   = error $ "Impossible happened while lifting " ++ show nm ++ " over " ++ show (k, x, i, r)

-- Lift a binary operation via SVal where second argument is an Int and returning a Bool
lift2IB :: (KnownNat n, BVIsNonZero n, HasKind (bv n), Integral (bv n), Show (bv n)) => String -> (SVal -> Int -> SVal) -> bv n -> Int -> Bool
lift2IB nm op x i = uc $ c x `op` i
  where k = kindOf x
        c = SVal k . Left . normCV . CV k . CInteger . toInteger
        uc (SVal _ (Left v)) = cvToBool v
        uc r                 = error $ "Impossible happened while lifting " ++ show nm ++ " over " ++ show (k, x, i, r)

-- | 'Bounded' instance for t'WordN'
instance (KnownNat n, BVIsNonZero n) => Bounded (WordN n) where
   minBound = WordN 0
   maxBound = let sz = intOfProxy (Proxy @n) in WordN $ 2 ^ sz - 1

-- | 'Bounded' instance for t'IntN'
instance (KnownNat n, BVIsNonZero n) => Bounded (IntN n) where
   minBound = let sz1 = intOfProxy (Proxy @n) - 1 in IntN $ - (2 ^ sz1)
   maxBound = let sz1 = intOfProxy (Proxy @n) - 1 in IntN $ 2 ^ sz1 - 1

-- | 'Num' instance for t'WordN'
instance (KnownNat n, BVIsNonZero n) => Num (WordN n) where
   (+)         = lift2 "(+)"    svPlus
   (-)         = lift2 "(*)"    svMinus
   (*)         = lift2 "(*)"    svTimes
   negate      = lift1 "signum" svUNeg
   abs         = lift1 "abs"    svAbs
   signum      = WordN . signum   . toInteger
   fromInteger = WordN . fromJust . svAsInteger . svInteger (kindOf (undefined :: WordN n))

-- | 'Num' instance for t'IntN'
instance (KnownNat n, BVIsNonZero n) => Num (IntN n) where
   (+)         = lift2 "(+)"    svPlus
   (-)         = lift2 "(*)"    svMinus
   (*)         = lift2 "(*)"    svTimes
   negate      = lift1 "signum" svUNeg
   abs         = lift1 "abs"    svAbs
   signum      = IntN . signum   . toInteger
   fromInteger = IntN . fromJust . svAsInteger . svInteger (kindOf (undefined :: IntN n))

-- | 'Enum' instance for t'WordN'
instance (KnownNat n, BVIsNonZero n) => Enum (WordN n) where
   succ x | x == maxBound = error $ "Enum.succ{" ++ show (kindOf x) ++ "}: tried to take `succ' of last tag in enumeration"
          | True          = x + 1

   pred x | x == minBound = error $ "Enum.pred{" ++ show (kindOf x) ++ "}: tried to take `pred' of first tag in enumeration"
          | True          = x - 1

   toEnum i | toInteger i < toInteger (minBound :: WordN n) = bad $ show i ++ " < minBound of " ++ show (minBound :: WordN n)
            | toInteger i > toInteger (maxBound :: WordN n) = bad $ show i ++ " > maxBound of " ++ show (maxBound :: WordN n)
            | True                                          = fromInteger (toInteger i)
     where bad why = error $ "Enum." ++ showType (Proxy @(WordN n)) ++ ".toEnum: bad argument: (" ++ why ++ ")"

   fromEnum = fromIntegral . toInteger

   enumFrom       = integralEnumFrom
   enumFromTo     = integralEnumFromTo
   enumFromThen   = integralEnumFromThen
   enumFromThenTo = integralEnumFromThenTo

-- | 'Enum' instance for t'IntN'
instance (KnownNat n, BVIsNonZero n) => Enum (IntN n) where
   succ x | x == maxBound = error $ "Enum.succ{" ++ show (kindOf x) ++ "}: tried to take `succ' of last tag in enumeration"
          | True          = x + 1

   pred x | x == minBound = error $ "Enum.pred{" ++ show (kindOf x) ++ "}: tried to take `pred' of first tag in enumeration"
          | True          = x - 1

   toEnum i | toInteger i < toInteger (minBound :: IntN n) = bad $ show i ++ " < minBound of " ++ show (minBound :: IntN n)
            | toInteger i > toInteger (maxBound :: IntN n) = bad $ show i ++ " > maxBound of " ++ show (maxBound :: IntN n)
            | True                                         = fromInteger (toInteger i)
     where bad why = error $ "Enum." ++ showType (Proxy @(IntN n)) ++ ".toEnum: bad argument: (" ++ why ++ ")"

   fromEnum = fromIntegral . toInteger

   enumFrom       = integralEnumFrom
   enumFromTo     = integralEnumFromTo
   enumFromThen   = integralEnumFromThen
   enumFromThenTo = integralEnumFromThenTo

-- | 'Real' instance for t'WordN'
instance (KnownNat n, BVIsNonZero n) => Real (WordN n) where
   toRational (WordN x) = toRational x

-- | 'Real' instance for t'IntN'
instance (KnownNat n, BVIsNonZero n) => Real (IntN n) where
   toRational (IntN x) = toRational x

-- | 'Integral' instance for t'WordN'
instance (KnownNat n, BVIsNonZero n) => Integral (WordN n) where
   toInteger (WordN x)           = x
   quotRem   (WordN x) (WordN y) = let (q, r) = quotRem x y in (WordN q, WordN r)

-- | 'Integral' instance for t'IntN'
instance (KnownNat n, BVIsNonZero n) => Integral (IntN n) where
   toInteger (IntN x)          = x
   quotRem   (IntN x) (IntN y) = let (q, r) = quotRem x y in (IntN q, IntN r)

--  'Bits' instance for t'WordN'
instance (KnownNat n, BVIsNonZero n) => Bits (WordN n) where
   (.&.)        = lift2   "(.&.)"      svAnd
   (.|.)        = lift2   "(.|.)"      svOr
   xor          = lift2   "xor"        svXOr
   complement   = lift1   "complement" svNot
   shiftL       = lift2I  "shiftL"     svShl
   shiftR       = lift2I  "shiftR"     svShr
   rotateL      = lift2I  "rotateL"    svRol
   rotateR      = lift2I  "rotateR"    svRor
   testBit      = lift2IB "svTestBit"  svTestBit
   bitSizeMaybe = Just . const (intOfProxy (Proxy @n))
   bitSize _    = intOfProxy (Proxy @n)
   isSigned     = hasSign . kindOf
   bit i        = 1 `shiftL` i
   popCount     = fromIntegral . popCount . toInteger

--  'Bits' instance for t'IntN'
instance (KnownNat n, BVIsNonZero n) => Bits (IntN n) where
   (.&.)        = lift2   "(.&.)"      svAnd
   (.|.)        = lift2   "(.|.)"      svOr
   xor          = lift2   "xor"        svXOr
   complement   = lift1   "complement" svNot
   shiftL       = lift2I  "shiftL"     svShl
   shiftR       = lift2I  "shiftR"     svShr
   rotateL      = lift2I  "rotateL"    svRol
   rotateR      = lift2I  "rotateR"    svRor
   testBit      = lift2IB "svTestBit"  svTestBit
   bitSizeMaybe = Just . const (intOfProxy (Proxy @n))
   bitSize _    = intOfProxy (Proxy @n)
   isSigned     = hasSign . kindOf
   bit i        = 1 `shiftL` i
   popCount     = fromIntegral . popCount . toInteger

-- | Quickcheck instance for WordN
instance KnownNat n => Arbitrary (WordN n) where
  arbitrary = (WordN . norm . abs) `fmap` arbitrary
    where sz = intOfProxy (Proxy @n)

          norm v | sz == 0 = 0
                 | True    = v .&. (((1 :: Integer) `shiftL` sz) - 1)

-- | Quickcheck instance for IntN
instance KnownNat n => Arbitrary (IntN n) where
  arbitrary = (IntN . norm) `fmap` arbitrary
    where sz = intOfProxy (Proxy @n)

          norm v | sz == 0 = 0
                 | True  = let rg = 2 ^ (sz - 1)
                           in case divMod v rg of
                                     (a, b) | even a -> b
                                     (_, b)          -> b - rg
