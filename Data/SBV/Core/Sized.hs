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
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.SBV.Core.Sized (
        -- * Type-sized unsigned bit-vectors
          SWord, WordN, sWord, sWord_, sWords
        -- * Type-sized signed bit-vectors
        , SInt, IntN, sInt, sInt_, sInts
        -- Bit-vector operations
        , bvExtract, (#), zeroExtend, signExtend, bvDrop, bvTake
        -- Non-zero constraint
        , IsNonZero
       ) where

import Data.Bits
import Data.Maybe (fromJust)
import Data.Proxy (Proxy(..))

import GHC.TypeLits
import Data.Kind

import Data.SBV.Core.Data
import Data.SBV.Core.Model
import Data.SBV.Core.Operations
import Data.SBV.Core.Symbolic

import Data.SBV.Control.Utils
import Data.SBV.SMT.SMT

-- Doctest only
-- $setup
-- >>> :set -XTypeApplications
-- >>> :set -XDataKinds
-- >>> import Data.SBV.Provers.Prover (prove)

-- | An unsigned bit-vector carrying its size info
newtype WordN (n :: Nat) = WordN Integer deriving (Eq, Ord)

-- | A symbolic unsigned bit-vector carrying its size info
type SWord (n :: Nat) = SBV (WordN n)

-- | Show instance for 'WordN'
instance Show (WordN n) where
  show (WordN v) = show v

-- | Grab the bit-size from the proxy
intOfProxy :: KnownNat n => Proxy n -> Int
intOfProxy = fromEnum . natVal

-- | Catch 0-width cases
type ZeroWidth = 'Text "Zero-width BV's are not allowed."

-- | Type family to create the appropriate non-zero constraint
type family IsNonZero (arg :: Nat) :: Constraint where
   IsNonZero 0 = TypeError ZeroWidth
   IsNonZero n = ()

-- | 'WordN' has a kind
instance (KnownNat n, IsNonZero n) => HasKind (WordN n) where
  kindOf _ = KBounded False (intOfProxy (Proxy @n))

-- | 'SymVal' instance for 'WordN'
instance (KnownNat n, IsNonZero n) => SymVal (WordN n) where
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
instance (KnownNat n, IsNonZero n) => HasKind (IntN n) where
  kindOf _ = KBounded True (intOfProxy (Proxy @n))

-- | 'SymVal' instance for 'IntN'
instance (KnownNat n, IsNonZero n) => SymVal (IntN n) where
   literal  x = genLiteral  (kindOf x) x
   mkSymVal   = genMkSymVar (kindOf (undefined :: IntN n))
   fromCV     = genFromCV

-- Lift a unary operation via SVal
lift1 :: (KnownNat n, IsNonZero n, HasKind (bv n), Integral (bv n), Show (bv n)) => String -> (SVal -> SVal) -> bv n -> bv n
lift1 nm op x = uc $ op (c x)
  where k = kindOf x
        c = SVal k . Left . CV k . CInteger . toInteger
        uc (SVal _ (Left (CV _ (CInteger v)))) = fromInteger v
        uc r                                   = error $ "Impossible happened while lifting " ++ show nm ++ " over " ++ show (k, x, r)

-- Lift a binary operation via SVal
lift2 :: (KnownNat n, IsNonZero n, HasKind (bv n), Integral (bv n), Show (bv n)) => String -> (SVal -> SVal -> SVal) -> bv n -> bv n -> bv n
lift2 nm op x y = uc $ c x `op` c y
  where k = kindOf x
        c = SVal k . Left . CV k . CInteger . toInteger
        uc (SVal _ (Left (CV _ (CInteger v)))) = fromInteger v
        uc r                                   = error $ "Impossible happened while lifting " ++ show nm ++ " over " ++ show (k, x, y, r)

-- Lift a binary operation via SVal where second argument is an Int
lift2I :: (KnownNat n, IsNonZero n, HasKind (bv n), Integral (bv n), Show (bv n)) => String -> (SVal -> Int -> SVal) -> bv n -> Int -> bv n
lift2I nm op x i = uc $ c x `op` i
  where k = kindOf x
        c = SVal k . Left . CV k . CInteger . toInteger
        uc (SVal _ (Left (CV _ (CInteger v)))) = fromInteger v
        uc r                                   = error $ "Impossible happened while lifting " ++ show nm ++ " over " ++ show (k, x, i, r)

-- Lift a binary operation via SVal where second argument is an Int and returning a Bool
lift2IB :: (KnownNat n, IsNonZero n, HasKind (bv n), Integral (bv n), Show (bv n)) => String -> (SVal -> Int -> SVal) -> bv n -> Int -> Bool
lift2IB nm op x i = uc $ c x `op` i
  where k = kindOf x
        c = SVal k . Left . CV k . CInteger . toInteger
        uc (SVal _ (Left v)) = cvToBool v
        uc r                 = error $ "Impossible happened while lifting " ++ show nm ++ " over " ++ show (k, x, i, r)

-- | 'Bounded' instance for 'WordN'
instance (KnownNat n, IsNonZero n) => Bounded (WordN n) where
   minBound = WordN 0
   maxBound = let sz = intOfProxy (Proxy @n) in WordN $ 2 ^ sz - 1

-- | 'Bounded' instance for 'IntN'
instance (KnownNat n, IsNonZero n) => Bounded (IntN n) where
   minBound = let sz1 = intOfProxy (Proxy @n) - 1 in IntN $ - (2 ^ sz1)
   maxBound = let sz1 = intOfProxy (Proxy @n) - 1 in IntN $ 2 ^ sz1 - 1

-- | 'Num' instance for 'WordN'
instance (KnownNat n, IsNonZero n) => Num (WordN n) where
   (+)         = lift2 "(+)"    svPlus
   (-)         = lift2 "(*)"    svMinus
   (*)         = lift2 "(*)"    svTimes
   negate      = lift1 "signum" svUNeg
   abs         = lift1 "abs"    svAbs
   signum      = WordN . signum   . toInteger
   fromInteger = WordN . fromJust . svAsInteger . svInteger (kindOf (undefined :: WordN n))

-- | 'Num' instance for 'IntN'
instance (KnownNat n, IsNonZero n) => Num (IntN n) where
   (+)         = lift2 "(+)"    svPlus
   (-)         = lift2 "(*)"    svMinus
   (*)         = lift2 "(*)"    svTimes
   negate      = lift1 "signum" svUNeg
   abs         = lift1 "abs"    svAbs
   signum      = IntN . signum   . toInteger
   fromInteger = IntN . fromJust . svAsInteger . svInteger (kindOf (undefined :: IntN n))

-- | 'Enum' instance for 'WordN'
instance (KnownNat n, IsNonZero n) => Enum (WordN n) where
   toEnum   = fromInteger  . toInteger
   fromEnum = fromIntegral . toInteger

-- | 'Enum' instance for 'IntN'
instance (KnownNat n, IsNonZero n) => Enum (IntN n) where
   toEnum   = fromInteger  . toInteger
   fromEnum = fromIntegral . toInteger

-- | 'Real' instance for 'WordN'
instance (KnownNat n, IsNonZero n) => Real (WordN n) where
   toRational (WordN x) = toRational x

-- | 'Real' instance for 'IntN'
instance (KnownNat n, IsNonZero n) => Real (IntN n) where
   toRational (IntN x) = toRational x

-- | 'Integral' instance for 'WordN'
instance (KnownNat n, IsNonZero n) => Integral (WordN n) where
   toInteger (WordN x)           = x
   quotRem   (WordN x) (WordN y) = let (q, r) = quotRem x y in (WordN q, WordN r)

-- | 'Integral' instance for 'IntN'
instance (KnownNat n, IsNonZero n) => Integral (IntN n) where
   toInteger (IntN x)          = x
   quotRem   (IntN x) (IntN y) = let (q, r) = quotRem x y in (IntN q, IntN r)

--  'Bits' instance for 'WordN'
instance (KnownNat n, IsNonZero n) => Bits (WordN n) where
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

--  'Bits' instance for 'IntN'
instance (KnownNat n, IsNonZero n) => Bits (IntN n) where
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

-- | 'SIntegral' instance for 'WordN'
instance (KnownNat n, IsNonZero n) => SIntegral (WordN n)

-- | 'SIntegral' instance for 'IntN'
instance (KnownNat n, IsNonZero n) => SIntegral (IntN n)

-- | 'SDivisible' instance for 'WordN'
instance (KnownNat n, IsNonZero n) => SDivisible (WordN n) where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

-- | 'SDivisible' instance for 'IntN'
instance (KnownNat n, IsNonZero n) => SDivisible (IntN n) where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

-- | 'SDivisible' instance for 'SWord'
instance (KnownNat n, IsNonZero n) => SDivisible (SWord n) where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

-- | 'SDivisible' instance for 'SInt'
instance (KnownNat n, IsNonZero n) => SDivisible (SInt n) where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

-- | 'SFiniteBits' instance for 'WordN'
instance (KnownNat n, IsNonZero n) => SFiniteBits (WordN n) where
   sFiniteBitSize _ = intOfProxy (Proxy @n)

-- | 'SFiniteBits' instance for 'IntN'
instance (KnownNat n, IsNonZero n) => SFiniteBits (IntN n) where
   sFiniteBitSize _ = intOfProxy (Proxy @n)

-- | Reading 'WordN' values in queries.
instance (KnownNat n, IsNonZero n) => SMTValue (WordN n) where
   sexprToVal e = WordN <$> sexprToVal e

-- | Reading 'IntN' values in queries.
instance (KnownNat n, IsNonZero n) => SMTValue (IntN n) where
   sexprToVal e = IntN <$> sexprToVal e

-- | Constructing models for 'WordN'
instance (KnownNat n, IsNonZero n) => SatModel (WordN n) where
  parseCVs = genParse (kindOf (undefined :: WordN n))

-- | Constructing models for 'IntN'
instance (KnownNat n, IsNonZero n) => SatModel (IntN n) where
  parseCVs = genParse (kindOf (undefined :: IntN n))

-- | Optimizing 'WordN'
instance (KnownNat n, IsNonZero n) => Metric (WordN n)

-- | Optimizing 'IntN'
instance (KnownNat n, IsNonZero n) => Metric (IntN n) where
  type MetricSpace (IntN n) = WordN n
  toMetricSpace    x        = sFromIntegral x + 2 ^ (intOfProxy (Proxy @n) - 1)
  fromMetricSpace  x        = sFromIntegral x - 2 ^ (intOfProxy (Proxy @n) - 1)

-- | Generalization of 'Data.SBV.sWord'
sWord :: (KnownNat n, IsNonZero n) => MonadSymbolic m => String -> m (SWord n)
sWord = symbolic

-- | Generalization of 'Data.SBV.sWord_'
sWord_ :: (KnownNat n, IsNonZero n) => MonadSymbolic m => m (SWord n)
sWord_ = free_

-- | Generalization of 'Data.SBV.sWord64s'
sWords :: (KnownNat n, IsNonZero n) => MonadSymbolic m => [String] -> m [SWord n]
sWords = symbolics

-- | Generalization of 'Data.SBV.sInt'
sInt :: (KnownNat n, IsNonZero n) => MonadSymbolic m => String -> m (SInt n)
sInt = symbolic

-- | Generalization of 'Data.SBV.sInt_'
sInt_ :: (KnownNat n, IsNonZero n) => MonadSymbolic m => m (SInt n)
sInt_ = free_

-- | Generalization of 'Data.SBV.sInts'
sInts :: (KnownNat n, IsNonZero n) => MonadSymbolic m => [String] -> m [SInt n]
sInts = symbolics

-- | Extract a portion of bits to form a smaller bit-vector.
--
-- >>> prove $ \x -> bvExtract (Proxy @7) (Proxy @3) (x :: SWord 12) .== bvDrop (Proxy @4) (bvTake (Proxy @9) x)
-- Q.E.D.
bvExtract :: forall i j n bv proxy. ( KnownNat n, IsNonZero n, SymVal (bv n)
                                    , KnownNat i
                                    , KnownNat j
                                    , i + 1 <= n
                                    , j <= i
                                    , IsNonZero (i - j + 1)
                                    ) => proxy i                -- ^ @i@: Start position, numbered from @n-1@ to @0@
                                      -> proxy j                -- ^ @j@: End position, numbered from @n-1@ to @0@, @j <= i@ must hold
                                      -> SBV (bv n)             -- ^ Input bit vector of size @n@
                                      -> SBV (bv (i - j + 1))   -- ^ Output is of size @i - j + 1@
bvExtract start end = SBV . svExtract i j . unSBV
   where i  = fromIntegral (natVal start)
         j  = fromIntegral (natVal end)

-- | Join two bitvectors.
--
-- >>> prove $ \x y -> x .== bvExtract (Proxy @79) (Proxy @71) ((x :: SWord 9) # (y :: SWord 71))
-- Q.E.D.
(#) :: ( KnownNat n, IsNonZero n, SymVal (bv n)
       , KnownNat m, IsNonZero m, SymVal (bv m)
       ) => SBV (bv n)                     -- ^ First input, of size @n@, becomes the left side
         -> SBV (bv m)                     -- ^ Second input, of size @m@, becomes the right side
         -> SBV (bv (n + m))               -- ^ Concatenation, of size @n+m@
n # m = SBV $ svJoin (unSBV n) (unSBV m)
infixr 5 #

-- | Zero extend a bit-vector.
--
-- >>> prove $ \x -> bvExtract (Proxy @20) (Proxy @12) (zeroExtend (x :: SInt 12) :: SInt 21) .== 0
-- Q.E.D.
zeroExtend :: forall n m bv. ( KnownNat n, IsNonZero n, SymVal (bv n)
                             , KnownNat m, IsNonZero m, SymVal (bv m)
                             , n + 1 <= m
                             , SIntegral (bv (m - n))
                             , IsNonZero (m - n)
                             ) => SBV (bv n)    -- ^ Input, of size @n@
                               -> SBV (bv m)    -- ^ Output, of size @m@. @n < m@ must hold
zeroExtend n = SBV $ svJoin (unSBV zero) (unSBV n)
  where zero :: SBV (bv (m - n))
        zero = literal 0

-- | Sign extend a bit-vector.
--
-- >>> prove $ \x -> sNot (msb x) .=> bvExtract (Proxy @20) (Proxy @12) (signExtend (x :: SInt 12) :: SInt 21) .== 0
-- Q.E.D.
-- >>> prove $ \x ->       msb x  .=> bvExtract (Proxy @20) (Proxy @12) (signExtend (x :: SInt 12) :: SInt 21) .== complement 0
-- Q.E.D.
signExtend :: forall n m bv. ( KnownNat n, IsNonZero n, SymVal (bv n)
                             , KnownNat m, IsNonZero m, SymVal (bv m)
                             , n + 1 <= m
                             , SFiniteBits (bv n)
                             , SIntegral   (bv (m - n))
                             , IsNonZero   (m - n)
                             ) => SBV (bv n)  -- ^ Input, of size @n@
                               -> SBV (bv m)  -- ^ Output, of size @m@. @n < m@ must hold
signExtend n = SBV $ svJoin (unSBV ext) (unSBV n)
  where zero, ones, ext :: SBV (bv (m - n))
        zero = literal 0
        ones = complement zero
        ext  = ite (msb n) ones zero

-- | Drop bits from the top of a bit-vector.
--
-- >>> prove $ \x -> bvDrop (Proxy @0) (x :: SWord 43) .== x
-- Q.E.D.
-- >>> prove $ \x -> bvDrop (Proxy @20) (x :: SWord 21) .== ite (lsb x) 1 0
-- Q.E.D.
bvDrop :: forall i n m bv proxy. ( KnownNat n, IsNonZero n
                                 , KnownNat i
                                 , i + 1 <= n
                                 , i + m - n <= 0
                                 , IsNonZero (n - i)
                                 ) => proxy i                    -- ^ @i@: Number of bits to drop. @i < n@ must hold.
                                   -> SBV (bv n)                 -- ^ Input, of size @n@
                                   -> SBV (bv m)                 -- ^ Output, of size @m@. @m = n - i@ holds.
bvDrop i = SBV . svExtract start 0 . unSBV
  where nv    = intOfProxy (Proxy @n)
        start = nv - fromIntegral (natVal i) - 1

-- | Take bits from the top of a bit-vector.
--
-- >>> prove $ \x -> bvTake (Proxy @13) (x :: SWord 13) .== x
-- Q.E.D.
-- >>> prove $ \x -> bvTake (Proxy @1) (x :: SWord 13) .== ite (msb x) 1 0
-- Q.E.D.
-- >>> prove $ \x -> bvTake (Proxy @4) x # bvDrop (Proxy @4) x .== (x :: SWord 23)
-- Q.E.D.
bvTake :: forall i n bv proxy. ( KnownNat n, IsNonZero n
                               , KnownNat i, IsNonZero i
                               , i <= n
                               ) => proxy i                  -- ^ @i@: Number of bits to take. @0 < i <= n@ must hold.
                                 -> SBV (bv n)               -- ^ Input, of size @n@
                                 -> SBV (bv i)               -- ^ Output, of size @i@
bvTake i = SBV . svExtract start end . unSBV
  where nv    = intOfProxy (Proxy @n)
        start = nv - 1
        end   = start - fromIntegral (natVal i) + 1
