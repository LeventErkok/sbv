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
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Data.SBV.Core.Sized (
        -- * Type-sized unsigned bit-vectors
          SWord
        -- * Type-sized signed bit-vectors
        , SInt
       ) where

import Data.Bits
import Data.Maybe (fromJust)
import Data.Proxy (Proxy(..))

import GHC.TypeLits

import Data.SBV.Core.Data
import Data.SBV.Core.Model
import Data.SBV.Core.Operations

import Data.SBV.Control.Utils
import Data.SBV.SMT.SMT

-- | An unsigned bit-vector carrying its size info
newtype WordN (n :: Nat) = WordN Integer deriving (Eq, Ord)

-- | A symbolic unsigned bit-vector carrying its size info
type SWord (n :: Nat) = SBV (WordN n)

-- | Show instance for 'WordN'
instance Show (WordN n) where
  show (WordN v) = show v

-- | Grab the bit-size from the proxy
intOfProxy :: (KnownNat n, 1 <= n) => Proxy n -> Int
intOfProxy = fromEnum . natVal

-- | 'WordN' has a kind
instance (KnownNat n, 1 <= n) => HasKind (WordN n) where
  kindOf _ = KBounded False (intOfProxy (Proxy @n))

-- | 'SymVal' instance for 'WordN'
instance (KnownNat n, 1 <= n) => SymVal (WordN n) where
   literal  x = genLiteral  (kindOf x) x
   mkSymVal   = genMkSymVar (kindOf (undefined :: WordN n))
   fromCV     = genFromCV

-- | A signed bit-vector carrying its size info
newtype IntN (n :: Nat) = IntN Integer deriving (Eq, Ord)

-- | A symbolic signed bit-vector carrying its size info
type SInt (n :: Nat) = SBV (IntN n)

-- | Show instance for 'IntN'
instance Show (IntN n) where
  show (IntN v) = show v

-- | 'IntN' has a kind
instance (KnownNat n, 1 <= n) => HasKind (IntN n) where
  kindOf _ = KBounded True (intOfProxy (Proxy @n))

-- | 'SymVal' instance for 'IntN'
instance (KnownNat n, 1 <= n) => SymVal (IntN n) where
   literal  x = genLiteral  (kindOf x) x
   mkSymVal   = genMkSymVar (kindOf (undefined :: IntN n))
   fromCV     = genFromCV

-- Lift a unary operation via SVal
lift1 :: (KnownNat n, 1 <= n, HasKind (bv n), Integral (bv n), Show (bv n)) => String -> (SVal -> SVal) -> bv n -> bv n
lift1 nm op x = uc $ op (c x)
  where k = kindOf x
        c = SVal k . Left . CV k . CInteger . toInteger
        uc (SVal _ (Left (CV _ (CInteger v)))) = fromInteger v
        uc r                                   = error $ "Impossible happened while lifting " ++ show nm ++ " over " ++ show (k, x, r)

-- Lift a binary operation via SVal
lift2 :: (KnownNat n, 1 <= n, HasKind (bv n), Integral (bv n), Show (bv n)) => String -> (SVal -> SVal -> SVal) -> bv n -> bv n -> bv n
lift2 nm op x y = uc $ c x `op` c y
  where k = kindOf x
        c = SVal k . Left . CV k . CInteger . toInteger
        uc (SVal _ (Left (CV _ (CInteger v)))) = fromInteger v
        uc r                                   = error $ "Impossible happened while lifting " ++ show nm ++ " over " ++ show (k, x, y, r)

-- Lift a binary operation via SVal where second argument is an Int
lift2I :: (KnownNat n, 1 <= n, HasKind (bv n), Integral (bv n), Show (bv n)) => String -> (SVal -> Int -> SVal) -> bv n -> Int -> bv n
lift2I nm op x i = uc $ c x `op` i
  where k = kindOf x
        c = SVal k . Left . CV k . CInteger . toInteger
        uc (SVal _ (Left (CV _ (CInteger v)))) = fromInteger v
        uc r                                   = error $ "Impossible happened while lifting " ++ show nm ++ " over " ++ show (k, x, i, r)

-- Lift a binary operation via SVal where second argument is an Int and returning a Bool
lift2IB :: (KnownNat n, 1 <= n, HasKind (bv n), Integral (bv n), Show (bv n)) => String -> (SVal -> Int -> SVal) -> bv n -> Int -> Bool
lift2IB nm op x i = uc $ c x `op` i
  where k = kindOf x
        c = SVal k . Left . CV k . CInteger . toInteger
        uc (SVal _ (Left v)) = cvToBool v
        uc r                 = error $ "Impossible happened while lifting " ++ show nm ++ " over " ++ show (k, x, i, r)

-- | 'Bounded' instance for 'WordN'
instance (KnownNat n, 1 <= n) => Bounded (WordN n) where
   minBound = WordN 0
   maxBound = WordN $ 2 ^ (intOfProxy (Proxy @n)) - 1

-- | 'Bounded' instance for 'IntN'
instance (KnownNat n, 1 <= n) => Bounded (IntN n) where
   minBound = IntN $ - (2 ^ (intOfProxy (Proxy @n) - 1))
   maxBound = IntN $ 2 ^ (intOfProxy (Proxy @n) - 1) - 1

-- | 'Num' instance for 'WordN'
instance (KnownNat n, 1 <= n) => Num (WordN n) where
   (+)         = lift2 "(+)"    svPlus
   (-)         = lift2 "(*)"    svMinus
   (*)         = lift2 "(*)"    svTimes
   negate      = lift1 "signum" svUNeg
   abs         = lift1 "abs"    svAbs
   signum      = WordN . signum   . toInteger
   fromInteger = WordN . fromJust . svAsInteger . svInteger (kindOf (undefined :: WordN n))

-- | 'Num' instance for 'IntN'
instance (KnownNat n, 1 <= n) => Num (IntN n) where
   (+)         = lift2 "(+)"    svPlus
   (-)         = lift2 "(*)"    svMinus
   (*)         = lift2 "(*)"    svTimes
   negate      = lift1 "signum" svUNeg
   abs         = lift1 "abs"    svAbs
   signum      = IntN . signum   . toInteger
   fromInteger = IntN . fromJust . svAsInteger . svInteger (kindOf (undefined :: IntN n))

-- | 'Enum' instance for 'WordN'
instance (KnownNat n, 1 <= n) => Enum (WordN n) where
   toEnum   = fromInteger  . toInteger
   fromEnum = fromIntegral . toInteger

-- | 'Enum' instance for 'IntN'
instance (KnownNat n, 1 <= n) => Enum (IntN n) where
   toEnum   = fromInteger  . toInteger
   fromEnum = fromIntegral . toInteger

-- | 'Real' instance for 'WordN'
instance (KnownNat n, 1 <= n) => Real (WordN n) where
   toRational (WordN x) = toRational x

-- | 'Real' instance for 'IntN'
instance (KnownNat n, 1 <= n) => Real (IntN n) where
   toRational (IntN x) = toRational x

-- | 'Integral' instance for 'WordN'
instance (KnownNat n, 1 <= n) => Integral (WordN n) where
   toInteger (WordN x)           = x
   quotRem   (WordN x) (WordN y) = let (q, r) = quotRem x y in (WordN q, WordN r)

-- | 'Integral' instance for 'IntN'
instance (KnownNat n, 1 <= n) => Integral (IntN n) where
   toInteger (IntN x)          = x
   quotRem   (IntN x) (IntN y) = let (q, r) = quotRem x y in (IntN q, IntN r)

--  'Bits' instance for 'WordN'
instance (KnownNat n, 1 <= n) => Bits (WordN n) where
   (.&.)        = lift2   "(.&.)"      svAnd
   (.|.)        = lift2   "(.|.)"      svOr
   xor          = lift2   "xor"        svXOr
   complement   = lift1   "complement" svNot
   shiftL       = lift2I  "shiftL"     svShl
   shiftR       = lift2I  "shiftR"     svShr
   rotateL      = lift2I  "rotateL"    svRol
   rotateR      = lift2I  "rotateR"    svRor
   testBit v i  = lift2IB "svTestBit" svTestBit v i
   bitSizeMaybe = Just . const (intOfProxy (Proxy @n))
   bitSize _    = intOfProxy (Proxy @n)
   isSigned     = hasSign . kindOf
   bit i        = 1 `shiftL` i
   popCount     = fromIntegral . popCount . toInteger

--  'Bits' instance for 'IntN'
instance (KnownNat n, 1 <= n) => Bits (IntN n) where
   (.&.)        = lift2   "(.&.)"      svAnd
   (.|.)        = lift2   "(.|.)"      svOr
   xor          = lift2   "xor"        svXOr
   complement   = lift1   "complement" svNot
   shiftL       = lift2I  "shiftL"     svShl
   shiftR       = lift2I  "shiftR"     svShr
   rotateL      = lift2I  "rotateL"    svRol
   rotateR      = lift2I  "rotateR"    svRor
   testBit v i  = lift2IB "svTestBit" svTestBit v i
   bitSizeMaybe = Just . const (intOfProxy (Proxy @n))
   bitSize _    = intOfProxy (Proxy @n)
   isSigned     = hasSign . kindOf
   bit i        = 1 `shiftL` i
   popCount     = fromIntegral . popCount . toInteger

-- | 'SIntegral' instance for 'WordN'
instance (KnownNat n, 1 <= n) => SIntegral (WordN n)

-- | 'SIntegral' instance for 'IntN'
instance (KnownNat n, 1 <= n) => SIntegral (IntN n)

-- | 'SDivisible' instance for 'WordN'
instance (KnownNat n, 1 <= n) => SDivisible (WordN n) where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

-- | 'SDivisible' instance for 'IntN'
instance (KnownNat n, 1 <= n) => SDivisible (IntN n) where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

-- | 'SDvisible' instance for 'SWordN'
instance (KnownNat n, 1 <= n) => SDivisible (SWord n) where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

-- | 'SDvisible' instance for 'SIntN'
instance (KnownNat n, 1 <= n) => SDivisible (SInt n) where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

-- | 'SFiniteBits' instance for 'WordN'
instance (KnownNat n, 1 <= n) => SFiniteBits (WordN n) where
   sFiniteBitSize _ = intOfProxy (Proxy @n)

-- | 'SFiniteBits' instance for 'IntN'
instance (KnownNat n, 1 <= n) => SFiniteBits (IntN n) where
   sFiniteBitSize _ = intOfProxy (Proxy @n)

-- | Reading 'WordN' values in queries.
instance (KnownNat n, 1 <= n) => SMTValue (WordN n) where
   sexprToVal e = WordN <$> sexprToVal e

-- | Reading 'IntN' values in queries.
instance (KnownNat n, 1 <= n) => SMTValue (IntN n) where
   sexprToVal e = IntN <$> sexprToVal e

-- | Constructing models for 'WordN'
instance (KnownNat n, 1 <= n) => SatModel (WordN n) where
  parseCVs = genParse (kindOf (undefined :: WordN n))

-- | Constructing models for 'IntN'
instance (KnownNat n, 1 <= n) => SatModel (IntN n) where
  parseCVs = genParse (kindOf (undefined :: IntN n))
