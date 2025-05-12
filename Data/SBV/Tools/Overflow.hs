-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.Overflow
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Implementation of overflow detection functions.
-- Based on: <http://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/z3prefix.pdf>
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                  #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE ImplicitParams       #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.Overflow (

         -- * Arithmetic overflows
         ArithOverflow(..), CheckedArithmetic(..)

         -- * Fast-checking of signed-multiplication overflow
         , signedMulOverflow

         -- * Cast overflows
       , sFromIntegralO, sFromIntegralChecked

    ) where

import Data.SBV.Core.Data
import Data.SBV.Core.Kind
import Data.SBV.Core.Model
import Data.SBV.Core.Operations

import GHC.TypeLits

import GHC.Stack

import Data.Int
import Data.Word
import Data.Proxy

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV
#endif

-- | Detecting overflow. Each function here will return 'sTrue' if the result will not fit in the target
-- type, i.e., if it overflows or underflows.
class ArithOverflow a where
  -- | Bit-vector addition. Unsigned addition can only overflow. Signed addition can underflow and overflow.
  --
  -- A tell tale sign of unsigned addition overflow is when the sum is less than minimum of the arguments.
  --
  -- >>> prove $ \x y -> bvAddO x (y::SWord16) .<=> x + y .< x `smin` y
  -- Q.E.D.
  bvAddO :: a -> a -> SBool

  -- | Bit-vector subtraction. Unsigned subtraction can only underflow. Signed subtraction can underflow and overflow.
  bvSubO :: a -> a -> SBool

  -- | Bit-vector multiplication. Unsigned multiplication can only overflow. Signed multiplication can underflow and overflow.
  bvMulO :: a -> a -> SBool

  -- | Bit-vector division. Unsigned division neither underflows nor overflows. Signed division can only overflow. In fact, for each
  -- signed bitvector type, there's precisely one pair that overflows, when @x@ is @minBound@ and @y@ is @-1@:
  --
  -- >>> allSat $ \x y -> x `bvDivO` (y::SInt8)
  -- Solution #1:
  --   s0 = -128 :: Int8
  --   s1 =   -1 :: Int8
  -- This is the only solution.
  bvDivO :: a -> a -> SBool

  -- | Bit-vector negation. Unsigned negation neither underflows nor overflows. Signed negation can only overflow, when the argument is
  -- @minBound@:
  --
  -- >>> prove $ \x -> x .== minBound .<=> bvNegO (x::SInt16)
  -- Q.E.D.
  bvNegO :: a -> SBool

instance ArithOverflow SWord8  where {bvAddO = l2 bvAddO; bvSubO = l2 bvSubO; bvMulO = l2 bvMulO; bvDivO = l2 bvDivO; bvNegO = l1 bvNegO}
instance ArithOverflow SWord16 where {bvAddO = l2 bvAddO; bvSubO = l2 bvSubO; bvMulO = l2 bvMulO; bvDivO = l2 bvDivO; bvNegO = l1 bvNegO}
instance ArithOverflow SWord32 where {bvAddO = l2 bvAddO; bvSubO = l2 bvSubO; bvMulO = l2 bvMulO; bvDivO = l2 bvDivO; bvNegO = l1 bvNegO}
instance ArithOverflow SWord64 where {bvAddO = l2 bvAddO; bvSubO = l2 bvSubO; bvMulO = l2 bvMulO; bvDivO = l2 bvDivO; bvNegO = l1 bvNegO}
instance ArithOverflow SInt8   where {bvAddO = l2 bvAddO; bvSubO = l2 bvSubO; bvMulO = l2 bvMulO; bvDivO = l2 bvDivO; bvNegO = l1 bvNegO}
instance ArithOverflow SInt16  where {bvAddO = l2 bvAddO; bvSubO = l2 bvSubO; bvMulO = l2 bvMulO; bvDivO = l2 bvDivO; bvNegO = l1 bvNegO}
instance ArithOverflow SInt32  where {bvAddO = l2 bvAddO; bvSubO = l2 bvSubO; bvMulO = l2 bvMulO; bvDivO = l2 bvDivO; bvNegO = l1 bvNegO}
instance ArithOverflow SInt64  where {bvAddO = l2 bvAddO; bvSubO = l2 bvSubO; bvMulO = l2 bvMulO; bvDivO = l2 bvDivO; bvNegO = l1 bvNegO}

instance (KnownNat n, BVIsNonZero n) => ArithOverflow (SWord n) where {bvAddO = l2 bvAddO; bvSubO = l2 bvSubO; bvMulO = l2 bvMulO; bvDivO = l2 bvDivO; bvNegO = l1 bvNegO}
instance (KnownNat n, BVIsNonZero n) => ArithOverflow (SInt  n) where {bvAddO = l2 bvAddO; bvSubO = l2 bvSubO; bvMulO = l2 bvMulO; bvDivO = l2 bvDivO; bvNegO = l1 bvNegO}

instance ArithOverflow SVal where
  bvAddO     = signPick2 (svMkOverflow2 (PlusOv False)) (svMkOverflow2 (PlusOv True))
  bvSubO     = signPick2 (svMkOverflow2 (SubOv  False)) (svMkOverflow2 (SubOv  True))
  bvMulO     = signPick2 (svMkOverflow2 (MulOv  False)) (svMkOverflow2 (MulOv  True))
  bvDivO     = signPick2 (const (const svFalse))        (svMkOverflow2 DivOv)           -- unsigned division doesn't overflow
  bvNegO     = signPick1 (const svFalse)                (svMkOverflow1 NegOv)           -- unsigned unary negation doesn't overflow

-- | A class of checked-arithmetic operations. These follow the usual arithmetic,
-- except make calls to 'Data.SBV.sAssert' to ensure no overflow/underflow can occur.
-- Use them in conjunction with 'Data.SBV.safe' to ensure no overflow can happen.
class (ArithOverflow (SBV a), Num a, SymVal a) => CheckedArithmetic a where
  (+!)          :: (?loc :: CallStack) => SBV a -> SBV a -> SBV a
  (-!)          :: (?loc :: CallStack) => SBV a -> SBV a -> SBV a
  (*!)          :: (?loc :: CallStack) => SBV a -> SBV a -> SBV a
  (/!)          :: (?loc :: CallStack) => SBV a -> SBV a -> SBV a
  negateChecked :: (?loc :: CallStack) => SBV a          -> SBV a

  infixl 6 +!, -!
  infixl 7 *!, /!

instance CheckedArithmetic Word8 where
  (+!)          = checkOp2 ?loc "addition"       (+)    bvAddO
  (-!)          = checkOp2 ?loc "subtraction"    (-)    bvSubO
  (*!)          = checkOp2 ?loc "multiplication" (*)    bvMulO
  (/!)          = checkOp2 ?loc "division"       sDiv   bvDivO
  negateChecked = checkOp1 ?loc "unary negation" negate bvNegO

instance CheckedArithmetic Word16 where
  (+!)          = checkOp2 ?loc "addition"       (+)    bvAddO
  (-!)          = checkOp2 ?loc "subtraction"    (-)    bvSubO
  (*!)          = checkOp2 ?loc "multiplication" (*)    bvMulO
  (/!)          = checkOp2 ?loc "division"       sDiv   bvDivO
  negateChecked = checkOp1 ?loc "unary negation" negate bvNegO

instance CheckedArithmetic Word32 where
  (+!)          = checkOp2 ?loc "addition"       (+)    bvAddO
  (-!)          = checkOp2 ?loc "subtraction"    (-)    bvSubO
  (*!)          = checkOp2 ?loc "multiplication" (*)    bvMulO
  (/!)          = checkOp2 ?loc "division"       sDiv   bvDivO
  negateChecked = checkOp1 ?loc "unary negation" negate bvNegO

instance CheckedArithmetic Word64 where
  (+!)          = checkOp2 ?loc "addition"       (+)    bvAddO
  (-!)          = checkOp2 ?loc "subtraction"    (-)    bvSubO
  (*!)          = checkOp2 ?loc "multiplication" (*)    bvMulO
  (/!)          = checkOp2 ?loc "division"       sDiv   bvDivO
  negateChecked = checkOp1 ?loc "unary negation" negate bvNegO

instance CheckedArithmetic Int8 where
  (+!)          = checkOp2 ?loc "addition"       (+)    bvAddO
  (-!)          = checkOp2 ?loc "subtraction"    (-)    bvSubO
  (*!)          = checkOp2 ?loc "multiplication" (*)    bvMulO
  (/!)          = checkOp2 ?loc "division"       sDiv   bvDivO
  negateChecked = checkOp1 ?loc "unary negation" negate bvNegO

instance CheckedArithmetic Int16 where
  (+!)          = checkOp2 ?loc "addition"       (+)    bvAddO
  (-!)          = checkOp2 ?loc "subtraction"    (-)    bvSubO
  (*!)          = checkOp2 ?loc "multiplication" (*)    bvMulO
  (/!)          = checkOp2 ?loc "division"       sDiv   bvDivO
  negateChecked = checkOp1 ?loc "unary negation" negate bvNegO

instance CheckedArithmetic Int32 where
  (+!)          = checkOp2 ?loc "addition"       (+)    bvAddO
  (-!)          = checkOp2 ?loc "subtraction"    (-)    bvSubO
  (*!)          = checkOp2 ?loc "multiplication" (*)    bvMulO
  (/!)          = checkOp2 ?loc "division"       sDiv   bvDivO
  negateChecked = checkOp1 ?loc "unary negation" negate bvNegO

instance CheckedArithmetic Int64 where
  (+!)          = checkOp2 ?loc "addition"       (+)    bvAddO
  (-!)          = checkOp2 ?loc "subtraction"    (-)    bvSubO
  (*!)          = checkOp2 ?loc "multiplication" (*)    bvMulO
  (/!)          = checkOp2 ?loc "division"       sDiv   bvDivO
  negateChecked = checkOp1 ?loc "unary negation" negate bvNegO

instance (KnownNat n, BVIsNonZero n) => CheckedArithmetic (WordN n) where
  (+!)          = checkOp2 ?loc "addition"       (+)    bvAddO
  (-!)          = checkOp2 ?loc "subtraction"    (-)    bvSubO
  (*!)          = checkOp2 ?loc "multiplication" (*)    bvMulO
  (/!)          = checkOp2 ?loc "division"       sDiv   bvDivO
  negateChecked = checkOp1 ?loc "unary negation" negate bvNegO

instance (KnownNat n, BVIsNonZero n) => CheckedArithmetic (IntN n) where
  (+!)          = checkOp2 ?loc "addition"       (+)    bvAddO
  (-!)          = checkOp2 ?loc "subtraction"    (-)    bvSubO
  (*!)          = checkOp2 ?loc "multiplication" (*)    bvMulO
  (/!)          = checkOp2 ?loc "division"       sDiv   bvDivO
  negateChecked = checkOp1 ?loc "unary negation" negate bvNegO

-- | Check all true
svAll :: [SVal] -> SVal
svAll = foldr svAnd svTrue

-- | Are all the bits between a b (inclusive) zero?
allZero :: Int -> Int -> SBV a -> SVal
allZero m n (SBV x)
  | m >= sz || n < 0 || m < n
  = error $ "Data.SBV.Tools.Overflow.allZero: Received unexpected parameters: " ++ show (m, n, sz)
  | True
  = svAll [svTestBit x i `svEqual` svFalse | i <- [m, m-1 .. n]]
  where sz = intSizeOf x

-- | Are all the bits between a b (inclusive) one?
allOne :: Int -> Int -> SBV a -> SVal
allOne m n (SBV x)
  | m >= sz || n < 0 || m < n
  = error $ "Data.SBV.Tools.Overflow.allOne: Received unexpected parameters: " ++ show (m, n, sz)
  | True
  = svAll [svTestBit x i `svEqual` svTrue | i <- [m, m-1 .. n]]
  where sz = intSizeOf x

-- | Detecting underflow/overflow conditions for casting between bit-vectors. The first output is the result,
-- the second component itself is a pair with the first boolean indicating underflow and the second indicating overflow.
--
-- >>> sFromIntegralO (256 :: SInt16) :: (SWord8, (SBool, SBool))
-- (0 :: SWord8,(False,True))
-- >>> sFromIntegralO (-2 :: SInt16) :: (SWord8, (SBool, SBool))
-- (254 :: SWord8,(True,False))
-- >>> sFromIntegralO (2 :: SInt16) :: (SWord8, (SBool, SBool))
-- (2 :: SWord8,(False,False))
-- >>> prove $ \x -> sFromIntegralO (x::SInt32) .== (sFromIntegral x :: SInteger, (sFalse, sFalse))
-- Q.E.D.
--
-- As the last example shows, converting to `sInteger` never underflows or overflows for any value.
sFromIntegralO :: forall a b. (Integral a, HasKind a, Num a, SymVal a, HasKind b, Num b, SymVal b) => SBV a -> (SBV b, (SBool, SBool))
sFromIntegralO x = case (kindOf x, kindOf (Proxy @b)) of
                     (KBounded False n, KBounded False m) -> (res, u2u n m)
                     (KBounded False n, KBounded True  m) -> (res, u2s n m)
                     (KBounded True n,  KBounded False m) -> (res, s2u n m)
                     (KBounded True n,  KBounded True  m) -> (res, s2s n m)
                     (KUnbounded,       KBounded s m)     -> (res, checkBounds s m)
                     (KBounded{},       KUnbounded)       -> (res, (sFalse, sFalse))
                     (KUnbounded,       KUnbounded)       -> (res, (sFalse, sFalse))
                     (kFrom,            kTo)              -> error $ "sFromIntegralO: Expected bounded-BV types, received: " ++ show (kFrom, kTo)

  where res :: SBV b
        res = sFromIntegral x

        checkBounds :: Bool -> Int -> (SBool, SBool)
        checkBounds signed sz = (ix .< literal lb, ix .> literal ub)
          where ix :: SInteger
                ix = sFromIntegral x

                s :: Integer
                s = fromIntegral sz

                ub :: Integer
                ub | signed = 2^(s - 1) - 1
                   | True   = 2^s       - 1

                lb :: Integer
                lb | signed = -ub-1
                   | True   = 0

        u2u :: Int -> Int -> (SBool, SBool)
        u2u n m = (underflow, overflow)
          where underflow  = sFalse
                overflow
                  | n <= m = sFalse
                  | True   = SBV $ svNot $ allZero (n-1) m x

        u2s :: Int -> Int -> (SBool, SBool)
        u2s n m = (underflow, overflow)
          where underflow = sFalse
                overflow
                  | m > n = sFalse
                  | True  = SBV $ svNot $ allZero (n-1) (m-1) x

        s2u :: Int -> Int -> (SBool, SBool)
        s2u n m = (underflow, overflow)
          where underflow = SBV $ (unSBV x `svTestBit` (n-1)) `svEqual` svTrue

                overflow
                  | m >= n - 1 = sFalse
                  | True       = SBV $ svAll [(unSBV x `svTestBit` (n-1)) `svEqual` svFalse, svNot $ allZero (n-1) m x]

        s2s :: Int -> Int -> (SBool, SBool)
        s2s n m = (underflow, overflow)
          where underflow
                  | m > n = sFalse
                  | True  = SBV $ svAll [(unSBV x `svTestBit` (n-1)) `svEqual` svTrue,  svNot $ allOne  (n-1) (m-1) x]

                overflow
                  | m > n = sFalse
                  | True  = SBV $ svAll [(unSBV x `svTestBit` (n-1)) `svEqual` svFalse, svNot $ allZero (n-1) (m-1) x]

-- | Version of 'sFromIntegral' that has calls to 'Data.SBV.sAssert' for checking no overflow/underflow can happen. Use it with a 'Data.SBV.safe' call.
sFromIntegralChecked :: forall a b. (?loc :: CallStack, Integral a, HasKind a, HasKind b, Num a, SymVal a, HasKind b, Num b, SymVal b) => SBV a -> SBV b
sFromIntegralChecked x = sAssert (Just ?loc) (msg "underflows") (sNot u)
                       $ sAssert (Just ?loc) (msg "overflows")  (sNot o)
                         r
  where kFrom = show $ kindOf x
        kTo   = show $ kindOf (Proxy @b)
        msg c = "Casting from " ++ kFrom ++ " to " ++ kTo ++ " " ++ c

        (r, (u, o)) = sFromIntegralO x

-- | signedMulOverflow: Checking if a signed bitvector multiplication can overflow. In general you should simply use 'bvMulO' for checking
-- signed multiplication overflow for bit-vectors. This is a function supported by SMTLib. Unfortunately, individual implementations have
-- different performance characteristics. For instance, bitwuzla has a fairly performant implementation of this, but z3 does not. (At least
-- not as of August 2024.) In cases where you can't use bitwuzla, you can use this implementation which has better performance.
signedMulOverflow :: forall n. ( KnownNat n,          BVIsNonZero n
                               , KnownNat (n+1),      BVIsNonZero (n+1)
                               , KnownNat (2+Log2 n), BVIsNonZero (2+Log2 n))
                               => SInt n -> SInt n -> SBool
signedMulOverflow x y = sNot zeroOut .&& overflow
  where zeroOut = x .== 0 .|| y .== 0

        prod :: SInt (n+1)
        prod = sFromIntegral x * sFromIntegral y

        nv :: Int
        nv = fromIntegral $ natVal (Proxy @n)

        prodN, prodNm1 :: SBool
        prodN   = prod `sTestBit` nv
        prodNm1 = prod `sTestBit` (nv-1)

        overflow =   nonSignBitPos x + nonSignBitPos y .> literal (fromIntegral (nv - 2))
                 .|| prodN .<+> prodNm1

        -- Find the position of the first non-sign bit. i.e., the first bit that differs from the msb.
        -- Position is 0 indexed. Note that if there's no differing bit, then you also get back 0.
        -- This is essentially an approximation of the logarithm of the magnitude of the number.
        --
        -- The result is at most N-2 for an N-bit word. Later we add two of these, so the maximum
        -- value we need to represent is 2N-4. This will require 1 + lg(2N-4) = 2 + log(N-1) bits.
        -- To suppor the case N=0, we return a (2 + log N) bit word.
        --
        -- Example for 3 bits:
        --
        --    000 -> 0  (no differing bit from 0; so we get 0)
        --    001 -> 0
        --    010 -> 1
        --    011 -> 1
        --    100 -> 1
        --    101 -> 1
        --    110 -> 0
        --    111 -> 0  (no differing bit from 1; so we get 0)
        nonSignBitPos :: ( KnownNat n,          BVIsNonZero n
                         , KnownNat (2+Log2 n), BVIsNonZero (2+Log2 n))
                         => SInt n -> SWord (2+Log2 n)
        nonSignBitPos w = walk 0 rest
          where (sign, rest) = case blastBE w of
                                 []     -> error $ "Impossible happened, blastBE returned no bits for " ++ show w
                                 (b:bs) -> (b, zip [0..] (reverse bs))

                walk sofar []          = sofar
                walk sofar ((i, b):bs) = walk (ite (b ./= sign) i sofar) bs

-- Helpers
l2 :: (SVal -> SVal -> SBool) -> SBV a -> SBV a -> SBool
l2 f (SBV a) (SBV b) = f a b

l1 :: (SVal -> SBool) -> SBV a -> SBool
l1 f (SBV a) = f a

signPick2 :: (SVal -> SVal -> SVal) -> (SVal -> SVal -> SVal) -> (SVal -> SVal -> SBool)
signPick2 fu fs a b
 | hasSign a = SBV (fs a b)
 | True      = SBV (fu a b)

signPick1 :: (SVal -> SVal) -> (SVal -> SVal) -> (SVal -> SBool)
signPick1 fu fs a
 | hasSign a = SBV (fs a)
 | True      = SBV (fu a)

checkOp1 :: (HasKind a, HasKind b) => CallStack -> String -> (a -> SBV b) -> (a -> SBool) -> a -> SBV b
checkOp1 loc w op cop a = sAssert (Just loc) (msg "overflows") (sNot (cop a)) $ op a
  where k = show $ kindOf a
        msg c = k ++ " " ++ w ++ " " ++ c

checkOp2 :: (HasKind a, HasKind c) => CallStack -> String -> (a -> b -> SBV c) -> (a -> b -> SBool) -> a -> b -> SBV c
checkOp2 loc w op cop a b = sAssert (Just loc) (msg "overflows")  (sNot (a `cop` b)) $ a `op` b
  where k = show $ kindOf a
        msg c = k ++ " " ++ w ++ " " ++ c
