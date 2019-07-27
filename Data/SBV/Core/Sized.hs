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

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Core.Sized (
        -- * Type-sized unsigned bit-vectors
          SWord, WordN, sWord, sWord_, sWords
        -- * Type-sized signed bit-vectors
        , SInt, IntN, sInt, sInt_, sInts
        -- Bit-vector operations
        , bvExtract, (#), zeroExtend, signExtend, bvDrop, bvTake
        -- Splitting and reconstructing from bytes
        , ByteConverter(..)
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

-- | A helper class to convert sized bit-vectors to/from bytes.
class ByteConverter a where
   -- | Convert to a sequence of bytes
   --
   -- >>> prove $ \a b c d -> toBytes ((fromBytes [a, b, c, d]) :: SWord 32) .== [a, b, c, d]
   -- Q.E.D.
   toBytes   :: a -> [SWord 8]

   -- | Convert from a sequence of bytes
   --
   -- >>> prove $ \r -> fromBytes (toBytes r) .== (r :: SWord 64)
   -- Q.E.D.
   fromBytes :: [SWord 8] -> a

-- NB. The following instances are automatically generated by buildUtils/genByteConverter.hs
-- It is possible to write these more compactly indeed, but this explicit form generates
-- better C code, and hence we allow the verbosity here.

-- | 'SWord' 8 instance for 'ByteConverter'
instance ByteConverter (SWord 8) where
   toBytes a = [a]

   fromBytes [x] = x
   fromBytes as  = error $ "fromBytes:SWord 8: Incorrect number of bytes: " ++ show (length as)

-- | 'SWord' 16 instance for 'ByteConverter'
instance ByteConverter (SWord 16) where
   toBytes a = [ bvExtract (Proxy @15) (Proxy  @8) a
               , bvExtract (Proxy  @7) (Proxy  @0) a
               ]

   fromBytes as
     | l == 2
     = (fromBytes :: [SWord 8] -> SWord 8) (take 1 as) # fromBytes (drop 1 as)
     | True
     = error $ "fromBytes:SWord 16: Incorrect number of bytes: " ++ show l
     where l = length as

-- | 'SWord' 32 instance for 'ByteConverter'
instance ByteConverter (SWord 32) where
   toBytes a = [ bvExtract (Proxy @31) (Proxy @24) a, bvExtract (Proxy @23) (Proxy @16) a, bvExtract (Proxy @15) (Proxy  @8) a, bvExtract (Proxy  @7) (Proxy  @0) a
               ]

   fromBytes as
     | l == 4
     = (fromBytes :: [SWord 8] -> SWord 16) (take 2 as) # fromBytes (drop 2 as)
     | True
     = error $ "fromBytes:SWord 32: Incorrect number of bytes: " ++ show l
     where l = length as

-- | 'SWord' 64 instance for 'ByteConverter'
instance ByteConverter (SWord 64) where
   toBytes a = [ bvExtract (Proxy @63) (Proxy @56) a, bvExtract (Proxy @55) (Proxy @48) a, bvExtract (Proxy @47) (Proxy @40) a, bvExtract (Proxy @39) (Proxy @32) a
               , bvExtract (Proxy @31) (Proxy @24) a, bvExtract (Proxy @23) (Proxy @16) a, bvExtract (Proxy @15) (Proxy  @8) a, bvExtract (Proxy  @7) (Proxy  @0) a
               ]

   fromBytes as
     | l == 8
     = (fromBytes :: [SWord 8] -> SWord 32) (take 4 as) # fromBytes (drop 4 as)
     | True
     = error $ "fromBytes:SWord 64: Incorrect number of bytes: " ++ show l
     where l = length as

-- | 'SWord' 128 instance for 'ByteConverter'
instance ByteConverter (SWord 128) where
   toBytes a = [ bvExtract (Proxy @127) (Proxy @120) a, bvExtract (Proxy @119) (Proxy @112) a, bvExtract (Proxy @111) (Proxy @104) a, bvExtract (Proxy @103) (Proxy  @96) a
               , bvExtract (Proxy  @95) (Proxy  @88) a, bvExtract (Proxy  @87) (Proxy  @80) a, bvExtract (Proxy  @79) (Proxy  @72) a, bvExtract (Proxy  @71) (Proxy  @64) a
               , bvExtract (Proxy  @63) (Proxy  @56) a, bvExtract (Proxy  @55) (Proxy  @48) a, bvExtract (Proxy  @47) (Proxy  @40) a, bvExtract (Proxy  @39) (Proxy  @32) a
               , bvExtract (Proxy  @31) (Proxy  @24) a, bvExtract (Proxy  @23) (Proxy  @16) a, bvExtract (Proxy  @15) (Proxy   @8) a, bvExtract (Proxy   @7) (Proxy   @0) a
               ]

   fromBytes as
     | l == 16
     = (fromBytes :: [SWord 8] -> SWord 64) (take 8 as) # fromBytes (drop 8 as)
     | True
     = error $ "fromBytes:SWord 128: Incorrect number of bytes: " ++ show l
     where l = length as

-- | 'SWord' 256 instance for 'ByteConverter'
instance ByteConverter (SWord 256) where
   toBytes a = [ bvExtract (Proxy @255) (Proxy @248) a, bvExtract (Proxy @247) (Proxy @240) a, bvExtract (Proxy @239) (Proxy @232) a, bvExtract (Proxy @231) (Proxy @224) a
               , bvExtract (Proxy @223) (Proxy @216) a, bvExtract (Proxy @215) (Proxy @208) a, bvExtract (Proxy @207) (Proxy @200) a, bvExtract (Proxy @199) (Proxy @192) a
               , bvExtract (Proxy @191) (Proxy @184) a, bvExtract (Proxy @183) (Proxy @176) a, bvExtract (Proxy @175) (Proxy @168) a, bvExtract (Proxy @167) (Proxy @160) a
               , bvExtract (Proxy @159) (Proxy @152) a, bvExtract (Proxy @151) (Proxy @144) a, bvExtract (Proxy @143) (Proxy @136) a, bvExtract (Proxy @135) (Proxy @128) a
               , bvExtract (Proxy @127) (Proxy @120) a, bvExtract (Proxy @119) (Proxy @112) a, bvExtract (Proxy @111) (Proxy @104) a, bvExtract (Proxy @103) (Proxy  @96) a
               , bvExtract (Proxy  @95) (Proxy  @88) a, bvExtract (Proxy  @87) (Proxy  @80) a, bvExtract (Proxy  @79) (Proxy  @72) a, bvExtract (Proxy  @71) (Proxy  @64) a
               , bvExtract (Proxy  @63) (Proxy  @56) a, bvExtract (Proxy  @55) (Proxy  @48) a, bvExtract (Proxy  @47) (Proxy  @40) a, bvExtract (Proxy  @39) (Proxy  @32) a
               , bvExtract (Proxy  @31) (Proxy  @24) a, bvExtract (Proxy  @23) (Proxy  @16) a, bvExtract (Proxy  @15) (Proxy   @8) a, bvExtract (Proxy   @7) (Proxy   @0) a
               ]

   fromBytes as
     | l == 32
     = (fromBytes :: [SWord 8] -> SWord 128) (take 16 as) # fromBytes (drop 16 as)
     | True
     = error $ "fromBytes:SWord 256: Incorrect number of bytes: " ++ show l
     where l = length as

-- | 'SWord' 512 instance for 'ByteConverter'
instance ByteConverter (SWord 512) where
   toBytes a = [ bvExtract (Proxy @511) (Proxy @504) a, bvExtract (Proxy @503) (Proxy @496) a, bvExtract (Proxy @495) (Proxy @488) a, bvExtract (Proxy @487) (Proxy @480) a
               , bvExtract (Proxy @479) (Proxy @472) a, bvExtract (Proxy @471) (Proxy @464) a, bvExtract (Proxy @463) (Proxy @456) a, bvExtract (Proxy @455) (Proxy @448) a
               , bvExtract (Proxy @447) (Proxy @440) a, bvExtract (Proxy @439) (Proxy @432) a, bvExtract (Proxy @431) (Proxy @424) a, bvExtract (Proxy @423) (Proxy @416) a
               , bvExtract (Proxy @415) (Proxy @408) a, bvExtract (Proxy @407) (Proxy @400) a, bvExtract (Proxy @399) (Proxy @392) a, bvExtract (Proxy @391) (Proxy @384) a
               , bvExtract (Proxy @383) (Proxy @376) a, bvExtract (Proxy @375) (Proxy @368) a, bvExtract (Proxy @367) (Proxy @360) a, bvExtract (Proxy @359) (Proxy @352) a
               , bvExtract (Proxy @351) (Proxy @344) a, bvExtract (Proxy @343) (Proxy @336) a, bvExtract (Proxy @335) (Proxy @328) a, bvExtract (Proxy @327) (Proxy @320) a
               , bvExtract (Proxy @319) (Proxy @312) a, bvExtract (Proxy @311) (Proxy @304) a, bvExtract (Proxy @303) (Proxy @296) a, bvExtract (Proxy @295) (Proxy @288) a
               , bvExtract (Proxy @287) (Proxy @280) a, bvExtract (Proxy @279) (Proxy @272) a, bvExtract (Proxy @271) (Proxy @264) a, bvExtract (Proxy @263) (Proxy @256) a
               , bvExtract (Proxy @255) (Proxy @248) a, bvExtract (Proxy @247) (Proxy @240) a, bvExtract (Proxy @239) (Proxy @232) a, bvExtract (Proxy @231) (Proxy @224) a
               , bvExtract (Proxy @223) (Proxy @216) a, bvExtract (Proxy @215) (Proxy @208) a, bvExtract (Proxy @207) (Proxy @200) a, bvExtract (Proxy @199) (Proxy @192) a
               , bvExtract (Proxy @191) (Proxy @184) a, bvExtract (Proxy @183) (Proxy @176) a, bvExtract (Proxy @175) (Proxy @168) a, bvExtract (Proxy @167) (Proxy @160) a
               , bvExtract (Proxy @159) (Proxy @152) a, bvExtract (Proxy @151) (Proxy @144) a, bvExtract (Proxy @143) (Proxy @136) a, bvExtract (Proxy @135) (Proxy @128) a
               , bvExtract (Proxy @127) (Proxy @120) a, bvExtract (Proxy @119) (Proxy @112) a, bvExtract (Proxy @111) (Proxy @104) a, bvExtract (Proxy @103) (Proxy  @96) a
               , bvExtract (Proxy  @95) (Proxy  @88) a, bvExtract (Proxy  @87) (Proxy  @80) a, bvExtract (Proxy  @79) (Proxy  @72) a, bvExtract (Proxy  @71) (Proxy  @64) a
               , bvExtract (Proxy  @63) (Proxy  @56) a, bvExtract (Proxy  @55) (Proxy  @48) a, bvExtract (Proxy  @47) (Proxy  @40) a, bvExtract (Proxy  @39) (Proxy  @32) a
               , bvExtract (Proxy  @31) (Proxy  @24) a, bvExtract (Proxy  @23) (Proxy  @16) a, bvExtract (Proxy  @15) (Proxy   @8) a, bvExtract (Proxy   @7) (Proxy   @0) a
               ]

   fromBytes as
     | l == 64
     = (fromBytes :: [SWord 8] -> SWord 256) (take 32 as) # fromBytes (drop 32 as)
     | True
     = error $ "fromBytes:SWord 512: Incorrect number of bytes: " ++ show l
     where l = length as

-- | 'SWord' 1024 instance for 'ByteConverter'
instance ByteConverter (SWord 1024) where
   toBytes a = [ bvExtract (Proxy @1023) (Proxy @1016) a, bvExtract (Proxy @1015) (Proxy @1008) a, bvExtract (Proxy @1007) (Proxy @1000) a, bvExtract (Proxy  @999) (Proxy  @992) a
               , bvExtract (Proxy  @991) (Proxy  @984) a, bvExtract (Proxy  @983) (Proxy  @976) a, bvExtract (Proxy  @975) (Proxy  @968) a, bvExtract (Proxy  @967) (Proxy  @960) a
               , bvExtract (Proxy  @959) (Proxy  @952) a, bvExtract (Proxy  @951) (Proxy  @944) a, bvExtract (Proxy  @943) (Proxy  @936) a, bvExtract (Proxy  @935) (Proxy  @928) a
               , bvExtract (Proxy  @927) (Proxy  @920) a, bvExtract (Proxy  @919) (Proxy  @912) a, bvExtract (Proxy  @911) (Proxy  @904) a, bvExtract (Proxy  @903) (Proxy  @896) a
               , bvExtract (Proxy  @895) (Proxy  @888) a, bvExtract (Proxy  @887) (Proxy  @880) a, bvExtract (Proxy  @879) (Proxy  @872) a, bvExtract (Proxy  @871) (Proxy  @864) a
               , bvExtract (Proxy  @863) (Proxy  @856) a, bvExtract (Proxy  @855) (Proxy  @848) a, bvExtract (Proxy  @847) (Proxy  @840) a, bvExtract (Proxy  @839) (Proxy  @832) a
               , bvExtract (Proxy  @831) (Proxy  @824) a, bvExtract (Proxy  @823) (Proxy  @816) a, bvExtract (Proxy  @815) (Proxy  @808) a, bvExtract (Proxy  @807) (Proxy  @800) a
               , bvExtract (Proxy  @799) (Proxy  @792) a, bvExtract (Proxy  @791) (Proxy  @784) a, bvExtract (Proxy  @783) (Proxy  @776) a, bvExtract (Proxy  @775) (Proxy  @768) a
               , bvExtract (Proxy  @767) (Proxy  @760) a, bvExtract (Proxy  @759) (Proxy  @752) a, bvExtract (Proxy  @751) (Proxy  @744) a, bvExtract (Proxy  @743) (Proxy  @736) a
               , bvExtract (Proxy  @735) (Proxy  @728) a, bvExtract (Proxy  @727) (Proxy  @720) a, bvExtract (Proxy  @719) (Proxy  @712) a, bvExtract (Proxy  @711) (Proxy  @704) a
               , bvExtract (Proxy  @703) (Proxy  @696) a, bvExtract (Proxy  @695) (Proxy  @688) a, bvExtract (Proxy  @687) (Proxy  @680) a, bvExtract (Proxy  @679) (Proxy  @672) a
               , bvExtract (Proxy  @671) (Proxy  @664) a, bvExtract (Proxy  @663) (Proxy  @656) a, bvExtract (Proxy  @655) (Proxy  @648) a, bvExtract (Proxy  @647) (Proxy  @640) a
               , bvExtract (Proxy  @639) (Proxy  @632) a, bvExtract (Proxy  @631) (Proxy  @624) a, bvExtract (Proxy  @623) (Proxy  @616) a, bvExtract (Proxy  @615) (Proxy  @608) a
               , bvExtract (Proxy  @607) (Proxy  @600) a, bvExtract (Proxy  @599) (Proxy  @592) a, bvExtract (Proxy  @591) (Proxy  @584) a, bvExtract (Proxy  @583) (Proxy  @576) a
               , bvExtract (Proxy  @575) (Proxy  @568) a, bvExtract (Proxy  @567) (Proxy  @560) a, bvExtract (Proxy  @559) (Proxy  @552) a, bvExtract (Proxy  @551) (Proxy  @544) a
               , bvExtract (Proxy  @543) (Proxy  @536) a, bvExtract (Proxy  @535) (Proxy  @528) a, bvExtract (Proxy  @527) (Proxy  @520) a, bvExtract (Proxy  @519) (Proxy  @512) a
               , bvExtract (Proxy  @511) (Proxy  @504) a, bvExtract (Proxy  @503) (Proxy  @496) a, bvExtract (Proxy  @495) (Proxy  @488) a, bvExtract (Proxy  @487) (Proxy  @480) a
               , bvExtract (Proxy  @479) (Proxy  @472) a, bvExtract (Proxy  @471) (Proxy  @464) a, bvExtract (Proxy  @463) (Proxy  @456) a, bvExtract (Proxy  @455) (Proxy  @448) a
               , bvExtract (Proxy  @447) (Proxy  @440) a, bvExtract (Proxy  @439) (Proxy  @432) a, bvExtract (Proxy  @431) (Proxy  @424) a, bvExtract (Proxy  @423) (Proxy  @416) a
               , bvExtract (Proxy  @415) (Proxy  @408) a, bvExtract (Proxy  @407) (Proxy  @400) a, bvExtract (Proxy  @399) (Proxy  @392) a, bvExtract (Proxy  @391) (Proxy  @384) a
               , bvExtract (Proxy  @383) (Proxy  @376) a, bvExtract (Proxy  @375) (Proxy  @368) a, bvExtract (Proxy  @367) (Proxy  @360) a, bvExtract (Proxy  @359) (Proxy  @352) a
               , bvExtract (Proxy  @351) (Proxy  @344) a, bvExtract (Proxy  @343) (Proxy  @336) a, bvExtract (Proxy  @335) (Proxy  @328) a, bvExtract (Proxy  @327) (Proxy  @320) a
               , bvExtract (Proxy  @319) (Proxy  @312) a, bvExtract (Proxy  @311) (Proxy  @304) a, bvExtract (Proxy  @303) (Proxy  @296) a, bvExtract (Proxy  @295) (Proxy  @288) a
               , bvExtract (Proxy  @287) (Proxy  @280) a, bvExtract (Proxy  @279) (Proxy  @272) a, bvExtract (Proxy  @271) (Proxy  @264) a, bvExtract (Proxy  @263) (Proxy  @256) a
               , bvExtract (Proxy  @255) (Proxy  @248) a, bvExtract (Proxy  @247) (Proxy  @240) a, bvExtract (Proxy  @239) (Proxy  @232) a, bvExtract (Proxy  @231) (Proxy  @224) a
               , bvExtract (Proxy  @223) (Proxy  @216) a, bvExtract (Proxy  @215) (Proxy  @208) a, bvExtract (Proxy  @207) (Proxy  @200) a, bvExtract (Proxy  @199) (Proxy  @192) a
               , bvExtract (Proxy  @191) (Proxy  @184) a, bvExtract (Proxy  @183) (Proxy  @176) a, bvExtract (Proxy  @175) (Proxy  @168) a, bvExtract (Proxy  @167) (Proxy  @160) a
               , bvExtract (Proxy  @159) (Proxy  @152) a, bvExtract (Proxy  @151) (Proxy  @144) a, bvExtract (Proxy  @143) (Proxy  @136) a, bvExtract (Proxy  @135) (Proxy  @128) a
               , bvExtract (Proxy  @127) (Proxy  @120) a, bvExtract (Proxy  @119) (Proxy  @112) a, bvExtract (Proxy  @111) (Proxy  @104) a, bvExtract (Proxy  @103) (Proxy   @96) a
               , bvExtract (Proxy   @95) (Proxy   @88) a, bvExtract (Proxy   @87) (Proxy   @80) a, bvExtract (Proxy   @79) (Proxy   @72) a, bvExtract (Proxy   @71) (Proxy   @64) a
               , bvExtract (Proxy   @63) (Proxy   @56) a, bvExtract (Proxy   @55) (Proxy   @48) a, bvExtract (Proxy   @47) (Proxy   @40) a, bvExtract (Proxy   @39) (Proxy   @32) a
               , bvExtract (Proxy   @31) (Proxy   @24) a, bvExtract (Proxy   @23) (Proxy   @16) a, bvExtract (Proxy   @15) (Proxy    @8) a, bvExtract (Proxy    @7) (Proxy    @0) a
               ]

   fromBytes as
     | l == 128
     = (fromBytes :: [SWord 8] -> SWord 512) (take 64 as) # fromBytes (drop 64 as)
     | True
     = error $ "fromBytes:SWord 1024: Incorrect number of bytes: " ++ show l
     where l = length as
