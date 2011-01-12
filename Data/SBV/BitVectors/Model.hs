-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.Model
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Instance declarations for our symbolic world
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}

module Data.SBV.BitVectors.Model (
    Mergeable(..), EqSymbolic(..), OrdSymbolic(..), BVDivisible(..)
  , bitValue, setBitTo, allEqual, allDifferent, oneIf, blastBE, blastLE
  , lsb, msb
  )
  where

import Data.Array
import Data.Bits
import Data.Int
import Data.List(genericLength, genericIndex, genericSplitAt, unzip4, unzip5, unzip6, unzip7)
import Data.Word
import Data.SBV.BitVectors.Bit
import Data.SBV.BitVectors.Data
import Data.SBV.Utils.Boolean
import Test.QuickCheck hiding((.&.), Result, (==>))

liftSym1 :: (State -> (Bool, Size) -> SW -> IO SW) -> (forall a. (Ord a, Bits a) => a -> a) -> SBV b -> SBV b
liftSym1 _   opC (SBV sgnsz (Left a))  = SBV sgnsz $ Left  $ mapCW opC a
liftSym1 opS _   a@(SBV sgnsz _)       = SBV sgnsz $ Right $ cache c
   where c st = do swa <- sbvToSW st a
                   opS st sgnsz swa

liftSym2 :: (State -> (Bool, Size) -> SW -> SW -> IO SW) -> (forall a. (Ord a, Bits a) => a -> a -> a) -> SBV b -> SBV b -> SBV b
liftSym2 _   opC (SBV sgnsz (Left a)) (SBV _ (Left b)) = SBV sgnsz $ Left  $ mapCW2 opC a b
liftSym2 opS _   a@(SBV sgnsz _)      b                = SBV sgnsz $ Right $ cache c
  where c st = do sw1 <- sbvToSW st a
                  sw2 <- sbvToSW st b
                  opS st sgnsz sw1 sw2

liftSym2B :: (State -> (Bool, Size) -> SW -> SW -> IO SW)
          -> (forall a. Ord a => a -> a -> Bool)
          -> SBV b -> SBV b -> SBool
liftSym2B _   opC (SBV _ (Left a)) (SBV _ (Left b)) = SBV (False, 1) $ Left  $ W1 $ bool2Bit $ liftCW2 opC a b
liftSym2B opS _   a                b                = SBV (False, 1) $ Right $ cache c
  where c st = do sw1 <- sbvToSW st a
                  sw2 <- sbvToSW st b
                  opS st (False, 1) sw1 sw2

liftSym1Bool :: (State -> (Bool, Size) -> SW -> IO SW)
             -> (Bool -> Bool)
             -> SBool -> SBool
liftSym1Bool _   opC (SBV _ (Left (W1 a))) = SBV (False, 1) $ Left  $ W1 $ bool2Bit $ opC $ bit2Bool a
liftSym1Bool opS _   a                     = SBV (False, 1) $ Right $ cache c
  where c st = do sw <- sbvToSW st a
                  opS st (False, 1) sw

liftSym2Bool :: (State -> (Bool, Size) -> SW -> SW -> IO SW)
             -> (Bool -> Bool -> Bool)
             -> SBool -> SBool -> SBool
liftSym2Bool _   opC (SBV _ (Left (W1 a))) (SBV _ (Left (W1 b))) = SBV (False, 1) $ Left  $ W1 $ bool2Bit $ bit2Bool a `opC` bit2Bool b
liftSym2Bool opS _   a                     b                     = SBV (False, 1) $ Right $ cache c
  where c st = do sw1 <- sbvToSW st a
                  sw2 <- sbvToSW st b
                  opS st (False, 1) sw1 sw2

mkSymOpSC :: (SW -> SW -> Maybe SW) -> Op -> State -> (Bool, Size) -> SW -> SW -> IO SW
mkSymOpSC shortCut op st sgnsz a b = maybe (newExpr st sgnsz (SBVApp op [a, b])) return (shortCut a b)

mkSymOp :: Op -> State -> (Bool, Size) -> SW -> SW -> IO SW
mkSymOp = mkSymOpSC (const (const Nothing))

mkSymOp1SC :: (SW -> Maybe SW) -> Op -> State -> (Bool, Size) -> SW -> IO SW
mkSymOp1SC shortCut op st sgnsz a = maybe (newExpr st sgnsz (SBVApp op [a])) return (shortCut a)

mkSymOp1 :: Op -> State -> (Bool, Size) -> SW -> IO SW
mkSymOp1 = mkSymOp1SC (const Nothing)

-- Symbolic-Word class instances
instance SymWord Bool where
  free    = mkSymSBV (False, 1) . Just
  free_   = mkSymSBV (False, 1) Nothing
  literal = SBV (False, 1) . Left . W1 . bool2Bit
  fromCW  = bit2Bool . wcToW1

instance SymWord Word8 where
  free    = mkSymSBV (False, 8) . Just
  free_   = mkSymSBV (False, 8) Nothing
  literal = SBV (False, 8)  . Left . W8
  fromCW  = wcToW8

instance SymWord Int8 where
  free    = mkSymSBV (True, 8) . Just
  free_   = mkSymSBV (True, 8) Nothing
  literal = SBV (True, 8)  . Left . I8
  fromCW  = wcToI8

instance SymWord Word16 where
  free    = mkSymSBV (False, 16) . Just
  free_   = mkSymSBV (False, 16) Nothing
  literal = SBV (False, 16) . Left . W16
  fromCW  = wcToW16

instance SymWord Int16 where
  free    = mkSymSBV (True, 16) . Just
  free_   = mkSymSBV (True, 16) Nothing
  literal = SBV (True, 16) . Left .  I16
  fromCW  = wcToI16

instance SymWord Word32 where
  free    = mkSymSBV (False, 32) . Just
  free_   = mkSymSBV (False, 32) Nothing
  literal = SBV (False, 32) . Left . W32
  fromCW  = wcToW32

instance SymWord Int32 where
  free    = mkSymSBV (True, 32) . Just
  free_   = mkSymSBV (True, 32) Nothing
  literal = SBV (True, 32) . Left . I32
  fromCW  = wcToI32

instance SymWord Word64 where
  free    = mkSymSBV (False, 64) . Just
  free_   = mkSymSBV (False, 64) Nothing
  literal = SBV (False, 64) . Left . W64
  fromCW  = wcToW64

instance SymWord Int64 where
  free    = mkSymSBV (True, 64) . Just
  free_   = mkSymSBV (True, 64) Nothing
  literal = SBV (True, 64) . Left . I64
  fromCW  = wcToI64

-- | Symbolic Equality. Note that we can't use Haskell's 'Eq' class since Haskell insists on returning Bool
-- Comparing symbolic values will necessarily return a symbolic value.
--
-- Minimal complete definition: '.=='
infix 4 .==, ./=
class EqSymbolic a where
  (.==), (./=) :: a -> a -> SBool
  -- minimal complete definition: .==
  x ./= y = bnot (x .== y)

-- | Symbolic Comparisons. Similar to 'Eq', we cannot implement Haskell's 'Ord' class
-- since there is no way to return an 'Ordering' value from a symbolic comparison.
-- Furthermore, 'OrdSymbolic' requires 'Mergeable' to implement if-then-else, for the
-- benefit of implementing symbolic versions of 'max' and 'min' functions.
--
-- Minimal complete definition: '.<'
infix 4 .<, .<=, .>, .>=
class (Mergeable a, EqSymbolic a) => OrdSymbolic a where
  (.<), (.<=), (.>), (.>=) :: a -> a -> SBool
  smin, smax :: a -> a -> a
  -- minimal complete definition: .<
  a .<= b    = a .< b ||| a .== b
  a .>  b    = b .<  a
  a .>= b    = b .<= a
  a `smin` b = ite (a .<= b) a b
  a `smax` b = ite (a .<= b) b a

{- We can't have a generic instance of the form:

instance Eq a => EqSymbolic a where
  x .== y = if x == y then true else false

even if we're willing to allow Flexible/undecidable instances..
This is because if we allow this it would imply EqSymbolic (SBV a);
since (SBV a) has to be Eq as it must be a Num. But this wouldn't be
the right choice obviously; as the Eq instance is bogus for SBV
for natural reasons..
-}

instance EqSymbolic (SBV a) where
  (.==) = liftSym2B (mkSymOpSC opt Equal)    (==)
             where opt x y = if x == y then Just trueSW else Nothing
  (./=) = liftSym2B (mkSymOpSC opt NotEqual) (/=)
             where opt x y = if x == y then Just falseSW else Nothing

instance SymWord a => OrdSymbolic (SBV a) where
  (.<)  = liftSym2B (mkSymOp LessThan)    (<)
  (.<=) = liftSym2B (mkSymOp LessEq)      (<=)
  (.>)  = liftSym2B (mkSymOp GreaterThan) (>)
  (.>=) = liftSym2B (mkSymOp GreaterEq)   (>=)

-- Bool
instance EqSymbolic Bool where
  x .== y = if x == y then true else false

-- Lists
instance EqSymbolic a => EqSymbolic [a] where
  []     .== []     = true
  (x:xs) .== (y:ys) = x .== y &&& xs .== ys
  _      .== _      = false

instance OrdSymbolic a => OrdSymbolic [a] where
  []     .< []     = false
  []     .< _      = true
  _      .< []     = false
  (x:xs) .< (y:ys) = x .< y ||| (x .== y &&& xs .< ys)

-- Maybe
instance EqSymbolic a => EqSymbolic (Maybe a) where
  Nothing .== Nothing = true
  Just a  .== Just b  = a .== b
  _       .== _       = false

instance (OrdSymbolic a) => OrdSymbolic (Maybe a) where
  Nothing .<  Nothing = false
  Nothing .<  _       = true
  Just _  .<  Nothing = false
  Just a  .<  Just b  = a .< b

-- Either
instance (EqSymbolic a, EqSymbolic b) => EqSymbolic (Either a b) where
  Left a  .== Left b  = a .== b
  Right a .== Right b = a .== b
  _       .== _       = false

instance (OrdSymbolic a, OrdSymbolic b) => OrdSymbolic (Either a b) where
  Left a  .< Left b  = a .< b
  Left _  .< Right _ = true
  Right _ .< Left _  = false
  Right a .< Right b = a .< b

-- 2-Tuple
instance (EqSymbolic a, EqSymbolic b) => EqSymbolic (a, b) where
  (a0, b0) .== (a1, b1) = a0 .== a1 &&& b0 .== b1

instance (OrdSymbolic a, OrdSymbolic b) => OrdSymbolic (a, b) where
  (a0, b0) .< (a1, b1) = a0 .< a1 ||| (a0 .== a1 &&& b0 .< b1)

-- 3-Tuple
instance (EqSymbolic a, EqSymbolic b, EqSymbolic c) => EqSymbolic (a, b, c) where
  (a0, b0, c0) .== (a1, b1, c1) = (a0, b0) .== (a1, b1) &&& c0 .== c1

instance (OrdSymbolic a, OrdSymbolic b, OrdSymbolic c) => OrdSymbolic (a, b, c) where
  (a0, b0, c0) .< (a1, b1, c1) = (a0, b0) .< (a1, b1) ||| ((a0, b0) .== (a1, b1) &&& c0 .< c1)

-- 4-Tuple
instance (EqSymbolic a, EqSymbolic b, EqSymbolic c, EqSymbolic d) => EqSymbolic (a, b, c, d) where
  (a0, b0, c0, d0) .== (a1, b1, c1, d1) = (a0, b0, c0) .== (a1, b1, c1) &&& d0 .== d1

instance (OrdSymbolic a, OrdSymbolic b, OrdSymbolic c, OrdSymbolic d) => OrdSymbolic (a, b, c, d) where
  (a0, b0, c0, d0) .< (a1, b1, c1, d1) = (a0, b0, c0) .< (a1, b1, c1) ||| ((a0, b0, c0) .== (a1, b1, c1) &&& d0 .< d1)

-- 5-Tuple
instance (EqSymbolic a, EqSymbolic b, EqSymbolic c, EqSymbolic d, EqSymbolic e) => EqSymbolic (a, b, c, d, e) where
  (a0, b0, c0, d0, e0) .== (a1, b1, c1, d1, e1) = (a0, b0, c0, d0) .== (a1, b1, c1, d1) &&& e0 .== e1

instance (OrdSymbolic a, OrdSymbolic b, OrdSymbolic c, OrdSymbolic d, OrdSymbolic e) => OrdSymbolic (a, b, c, d, e) where
  (a0, b0, c0, d0, e0) .< (a1, b1, c1, d1, e1) = (a0, b0, c0, d0) .< (a1, b1, c1, d1) ||| ((a0, b0, c0, d0) .== (a1, b1, c1, d1) &&& e0 .< e1)

-- 6-Tuple
instance (EqSymbolic a, EqSymbolic b, EqSymbolic c, EqSymbolic d, EqSymbolic e, EqSymbolic f) => EqSymbolic (a, b, c, d, e, f) where
  (a0, b0, c0, d0, e0, f0) .== (a1, b1, c1, d1, e1, f1) = (a0, b0, c0, d0, e0) .== (a1, b1, c1, d1, e1) &&& f0 .== f1

instance (OrdSymbolic a, OrdSymbolic b, OrdSymbolic c, OrdSymbolic d, OrdSymbolic e, OrdSymbolic f) => OrdSymbolic (a, b, c, d, e, f) where
  (a0, b0, c0, d0, e0, f0) .< (a1, b1, c1, d1, e1, f1) =    (a0, b0, c0, d0, e0) .<  (a1, b1, c1, d1, e1)
                                                       ||| ((a0, b0, c0, d0, e0) .== (a1, b1, c1, d1, e1) &&& f0 .< f1)

-- 7-Tuple
instance (EqSymbolic a, EqSymbolic b, EqSymbolic c, EqSymbolic d, EqSymbolic e, EqSymbolic f, EqSymbolic g) => EqSymbolic (a, b, c, d, e, f, g) where
  (a0, b0, c0, d0, e0, f0, g0) .== (a1, b1, c1, d1, e1, f1, g1) = (a0, b0, c0, d0, e0, f0) .== (a1, b1, c1, d1, e1, f1) &&& g0 .== g1

instance (OrdSymbolic a, OrdSymbolic b, OrdSymbolic c, OrdSymbolic d, OrdSymbolic e, OrdSymbolic f, OrdSymbolic g) => OrdSymbolic (a, b, c, d, e, f, g) where
  (a0, b0, c0, d0, e0, f0, g0) .< (a1, b1, c1, d1, e1, f1, g1) =    (a0, b0, c0, d0, e0, f0) .<  (a1, b1, c1, d1, e1, f1)
                                                               ||| ((a0, b0, c0, d0, e0, f0) .== (a1, b1, c1, d1, e1, f1) &&& g0 .< g1)

-- Boolean combinators
instance Boolean SBool where
  true  = literal True
  false = literal False
  bnot  = liftSym1Bool (mkSymOp1 Not) not
  (&&&) = liftSym2Bool (mkSymOpSC opt And) (&&)
            where opt x y
                   | x == falseSW || y == falseSW = Just falseSW
                   | x == trueSW                  = Just y
                   | y == trueSW                  = Just x
                   | True                         = Nothing
  (|||) = liftSym2Bool (mkSymOpSC opt Or)  (||)
            where opt x y
                   | x == trueSW || y == trueSW = Just trueSW
                   | x == falseSW               = Just y
                   | y == falseSW               = Just x
                   | True                       = Nothing
  (<+>) = liftSym2Bool (mkSymOpSC opt XOr) (<+>)
            where opt x y
                   | x == y = Just falseSW
                   | True   = Nothing

-- | Returns (symbolic) true if all the elements of the given list are different
allDifferent :: (Eq a, SymWord a) => [SBV a] -> SBool
allDifferent (x:xs@(_:_)) = bAll ((./=) x) xs &&& allDifferent xs
allDifferent _            = true

-- | Returns (symbolic) true if all the elements of the given list are the same
allEqual :: (Eq a, SymWord a) => [SBV a] -> SBool
allEqual (x:xs@(_:_))     = bAll ((.==) x) xs
allEqual _                = true

-- | Returns 1 if the boolean is true, otherwise 0
oneIf :: (Num a, SymWord a) => SBool -> SBV a
oneIf t = ite t 1 0

-- Num instance for symbolic words
instance (Ord a, Num a, SymWord a) => Num (SBV a) where
  fromInteger = literal . fromIntegral
  (+) = liftSym2 (mkSymOp Plus)  (+)
  (*) = liftSym2 (mkSymOp Times) (*)
  (-) = liftSym2 (mkSymOp Minus) (-)
  abs a
   | hasSign a = ite (a .< 0) (-a) a
   | True      = a
  signum a
   | hasSign a = ite (a .< 0) (-1) (ite (a .== 0) 0 1)
   | True      = oneIf (a ./= 0)

-- NB. The default definition of "testBit" relies on equality,
-- which is not available for symbolic SBV's. There is no
-- way to implement testBit to return Bool, obviously; instead use bitValue
instance (Bits a, SymWord a) => Bits (SBV a) where
  (.&.)                    = liftSym2 (mkSymOp  And) (.&.)
  (.|.)                    = liftSym2 (mkSymOp  Or)  (.|.)
  xor                      = liftSym2 (mkSymOp  XOr) xor
  complement               = liftSym1 (mkSymOp1 Not) complement
  bitSize  (SBV (_ ,s) _)  = s
  isSigned (SBV (b, _) _)  = b
  shiftL x y
    | y < 0                = shiftR x (-y)
    | y == 0               = x
    | True                 = liftSym1 (mkSymOp1 (Shl y)) (`shiftL` y) x
  shiftR x y
    | y < 0                = shiftL x (-y)
    | y == 0               = x
    | True                 = liftSym1 (mkSymOp1 (Shr y)) (`shiftR` y) x
  rotateL x y
    | y < 0                = rotateR x (-y)
    | y == 0               = x
    | True                 = liftSym1 (mkSymOp1 (Rol y)) (`rotateL` y) x
  rotateR x y
    | y < 0                = rotateL x (-y)
    | y == 0               = x
    | True                 = liftSym1 (mkSymOp1 (Ror y)) (`rotateR` y) x

-- | Replacement for 'testBit'. Since 'testBit' requires a 'Bool' to be returned,
-- we cannot implement it for symbolic words. Index 0 is the least-significant bit.
bitValue :: (Bits a, SymWord a) => SBV a -> Int -> SBool
bitValue x i = (x .&. bit i) ./= 0

-- | Generalization of 'setBit' based on a symbolic boolean. Note that 'setBit' and
-- 'clearBit' are still available on Symbolic words, this operation comes handy when
-- the condition to set/clear happens to be symbolic
setBitTo :: (Bits a, SymWord a) => SBV a -> Int -> SBool -> SBV a
setBitTo x i b = ite b (setBit x i) (clearBit x i)

-- | Little-endian blasting of a word into its bits. Also see the 'FromBits' class
blastLE :: (Bits a, SymWord a) => SBV a -> [SBool]
blastLE x = map (bitValue x) [0 .. (sizeOf x)-1]

-- | Big-endian blasting of a word into its bits. Also see the 'FromBits' class
blastBE :: (Bits a, SymWord a) => SBV a -> [SBool]
blastBE = reverse . blastLE

-- | Least significant bit of a word, always stored at index 0
lsb :: (Bits a, SymWord a) => SBV a -> SBool
lsb x = bitValue x 0

-- | Most significant bit of a word, always stored at the last position
msb :: (Bits a, SymWord a) => SBV a -> SBool
msb x = bitValue x ((sizeOf x) - 1)

-- | The 'BVDivisible' class captures the essence of division of words.
-- Unfortunately we cannot use Haskell's 'Integral' class since the 'Real'
-- and 'Enum' superclasses are not implementable for symbolic bit-vectors.
-- However, 'quotRem' makes perfect sense, and the 'BVDivisible' class captures
-- this operation. One issue is how division by 0 behaves. The verification
-- technology requires total functions, and there are several design choices
-- here. We follow Isabelle/HOL approach of assigning the value 0 for division
-- by 0. Therefore, we impose the following law:
--
--     @ x `bvQuotRem` 0 = (0, x) @
--
-- Note that our instances implement this law even when @x@ is @0@ itself.
--
-- Minimal complete definition: 'bvQuotRem'
class BVDivisible a where
  bvQuotRem :: a -> a -> (a, a)

instance BVDivisible Word64 where
  bvQuotRem x 0 = (0, x)
  bvQuotRem x y = x `quotRem` y

instance BVDivisible Word32 where
  bvQuotRem x 0 = (0, x)
  bvQuotRem x y = x `quotRem` y

instance BVDivisible Word16 where
  bvQuotRem x 0 = (0, x)
  bvQuotRem x y = x `quotRem` y

instance BVDivisible Word8 where
  bvQuotRem x 0 = (0, x)
  bvQuotRem x y = x `quotRem` y

instance BVDivisible SWord64 where
  bvQuotRem = liftQRem

instance BVDivisible SWord32 where
  bvQuotRem = liftQRem

instance BVDivisible SWord16 where
  bvQuotRem = liftQRem

instance BVDivisible SWord8 where
  bvQuotRem = liftQRem

liftQRem :: (SymWord a, Num a, BVDivisible a) => SBV a -> SBV a -> (SBV a, SBV a)
liftQRem x y = ite (y .== 0) (0, x) (qr x y)
  where qr (SBV sgnsz (Left a)) (SBV _ (Left b)) = let (q, r) = mapCW22 bvQuotRem a b in (SBV sgnsz (Left q), SBV sgnsz (Left r))
        qr a@(SBV sgnsz _)      b                = (SBV sgnsz (Right (cache (mk Quot))), SBV sgnsz (Right (cache (mk Rem))))
                where mk o st = do sw1 <- sbvToSW st a
                                   sw2 <- sbvToSW st b
                                   mkSymOp o st sgnsz sw1 sw2
        mapCW22 :: (forall a. (Ord a, Bits a, BVDivisible a) => a -> a -> (a, a)) -> CW -> CW -> (CW, CW)
        mapCW22 f (W8  a) (W8  b) = let (r1, r2) = a `f` b in (W8  r1, W8  r2)
        mapCW22 f (W16 a) (W16 b) = let (r1, r2) = a `f` b in (W16 r1, W16 r2)
        mapCW22 f (W32 a) (W32 b) = let (r1, r2) = a `f` b in (W32 r1, W32 r2)
        mapCW22 f (W64 a) (W64 b) = let (r1, r2) = a `f` b in (W64 r1, W64 r2)
        mapCW22 _ a       b       = error $ "SBV.liftQRem: impossible, unexpected args received: " ++ show (a, b)

-- Quickcheck interface

-- The Arbitrary instance for SFunArray returns an array initialized
-- to an arbitrary element
instance (SymWord b, Arbitrary b) => Arbitrary (SFunArray a b) where
  arbitrary = arbitrary >>= \r -> return $ SFunArray (const r)

instance (SymWord a, Arbitrary a) => Arbitrary (SBV a) where
  arbitrary = arbitrary >>= return . literal

-- |  Symbolic choice operator, parameterized via a class
-- 'select' is a total-indexing function, with the default.
--
-- Minimal complete definition: 'symbolicMerge'
class Mergeable a where
   -- | Merge two values based on the condition
   symbolicMerge :: SBool -> a -> a -> a
   -- | Choose one or the other element, based on the condition.
   -- This is similar to 'symbolicMerge', but it has a default
   -- implementation that makes sure it's short-cut if the condition is concrete
   ite           :: SBool -> a -> a -> a
   -- | Total indexing operation. @select xs default index@ is intuitively
   -- the same as @xs !! index@, except it evaluates to @default@ if @index@
   -- overflows
   select        :: (Bits b, SymWord b, Integral b) => [a] -> a -> SBV b -> a
   -- default definitions
   ite s a b
    | Just t <- unliteral s = if t then a else b
    | True                  = symbolicMerge s a b
   select [] err _   = err
   select xs err ind
    | hasSign ind    = ite (ind .< 0) err $ result
    | True           = result
    where result = go xs $ reverse (zip [(0::Integer)..] bits)
          bits   = map (ind `bitValue`) [0 .. bitSize ind - 1]
          go []    _            = err
          go (x:_) []           = x
          go elts  ((n, b):nbs) = let (ys, zs) = genericSplitAt ((2::Integer) ^ n) elts
                                  in ite b (go zs nbs) (go ys nbs)

-- SBV
instance SymWord a => Mergeable (SBV a) where
  symbolicMerge t a b
   | Just c1 <- unliteral a, Just c2 <- unliteral b, c1 == c2
   = a
   | True
   = SBV sgnsz $ Right $ cache c
    where sgnsz = (hasSign a, sizeOf a)
          c st = do swt <- sbvToSW st t
                    case () of
                      () | swt == trueSW  -> sbvToSW st a
                      () | swt == falseSW -> sbvToSW st b
                      () -> do swa <- sbvToSW st a
                               swb <- sbvToSW st b
                               if swa == swb
                                  then return swa
                                  else newExpr st sgnsz (SBVApp Ite [swt, swa, swb])
  -- Custom version of select that translates to SMT-Lib tables at the base type of words
  select xs err ind
    | Just i <- unliteral ind
    = let i' :: Integer
          i' = fromIntegral i
      in if i' < 0 || i' >= genericLength xs then err else genericIndex xs i'
  select [] err _   = err
  select xs err ind = SBV sgnsz $ Right $ cache r
     where sind  = sizeOf ind
           serr  = sizeOf err
           sgnsz = (hasSign err, serr)
           r st  = do sws <- mapM (sbvToSW st) xs
                      swe <- sbvToSW st err
                      if all (== swe) sws  -- off-chance that all elts are the same
                         then return swe
                         else do idx <- getTableIndex st sind serr sws
                                 swi <- sbvToSW st ind
                                 let len = length xs
                                 newExpr st sgnsz (SBVApp (LkUp (idx, sind, sizeOf err, len) swi swe) [])

-- Unit
instance Mergeable () where
   symbolicMerge _ _ _ = ()
   select _ _ _ = ()

-- Mergeable instances for List/Maybe/Either/Array are useful, but can
-- throw exceptions if there is no structural matching of the results
-- It's a question whether we should really keep them..

-- Lists
instance Mergeable a => Mergeable [a] where
  symbolicMerge t xs ys
    | lxs == lys = zipWith (symbolicMerge t) xs ys
    | True       = error $ "SBV.Mergeable.List: No least-upper-bound for lists of differing size " ++ show (lxs, lys)
    where (lxs, lys) = (length xs, length ys)

-- Maybe
instance Mergeable a => Mergeable (Maybe a) where
  symbolicMerge _ Nothing  Nothing  = Nothing
  symbolicMerge t (Just a) (Just b) = Just $ symbolicMerge t a b
  symbolicMerge _ a b = error $ "SBV.Mergeable.Maybe: No least-upper-bound for " ++ show (k a, k b)
      where k Nothing = "Nothing"
            k _       = "Just"

-- Either
instance (Mergeable a, Mergeable b) => Mergeable (Either a b) where
  symbolicMerge t (Left a)  (Left b)  = Left  $ symbolicMerge t a b
  symbolicMerge t (Right a) (Right b) = Right $ symbolicMerge t a b
  symbolicMerge _ a b = error $ "SBV.Mergeable.Either: No least-upper-bound for " ++ show (k a, k b)
     where k (Left _)  = "Left"
           k (Right _) = "Right"

-- Arrays
instance (Ix a, Mergeable b) => Mergeable (Array a b) where
  symbolicMerge t a b
    | ba == bb = listArray ba (zipWith (symbolicMerge t) (elems a) (elems b))
    | True     = error $ "SBV.Mergeable.Array: No least-upper-bound for rangeSizes" ++ show (k ba, k bb)
    where [ba, bb] = map bounds [a, b]
          k = rangeSize

-- Functions
instance Mergeable b => Mergeable (a -> b) where
  symbolicMerge t f g = \x -> symbolicMerge t (f x) (g x)
  select xs err ind   = \x -> select (map ($ x) xs) (err x) ind

-- 2-Tuple
instance (Mergeable a, Mergeable b) => Mergeable (a, b) where
  symbolicMerge t (i0, i1) (j0, j1) = (i i0 j0, i i1 j1)
    where i a b = symbolicMerge t a b
  select xs (err1, err2) ind = (select as err1 ind, select bs err2 ind)
    where (as, bs) = unzip xs

-- 3-Tuple
instance (Mergeable a, Mergeable b, Mergeable c) => Mergeable (a, b, c) where
  symbolicMerge t (i0, i1, i2) (j0, j1, j2) = (i i0 j0, i i1 j1, i i2 j2)
    where i a b = symbolicMerge t a b
  select xs (err1, err2, err3) ind = (select as err1 ind, select bs err2 ind, select cs err3 ind)
    where (as, bs, cs) = unzip3 xs

-- 4-Tuple
instance (Mergeable a, Mergeable b, Mergeable c, Mergeable d) => Mergeable (a, b, c, d) where
  symbolicMerge t (i0, i1, i2, i3) (j0, j1, j2, j3) = (i i0 j0, i i1 j1, i i2 j2, i i3 j3)
    where i a b = symbolicMerge t a b
  select xs (err1, err2, err3, err4) ind = (select as err1 ind, select bs err2 ind, select cs err3 ind, select ds err4 ind)
    where (as, bs, cs, ds) = unzip4 xs

-- 5-Tuple
instance (Mergeable a, Mergeable b, Mergeable c, Mergeable d, Mergeable e) => Mergeable (a, b, c, d, e) where
  symbolicMerge t (i0, i1, i2, i3, i4) (j0, j1, j2, j3, j4) = (i i0 j0, i i1 j1, i i2 j2, i i3 j3, i i4 j4)
    where i a b = symbolicMerge t a b
  select xs (err1, err2, err3, err4, err5) ind = (select as err1 ind, select bs err2 ind, select cs err3 ind, select ds err4 ind, select es err5 ind)
    where (as, bs, cs, ds, es) = unzip5 xs

-- 6-Tuple
instance (Mergeable a, Mergeable b, Mergeable c, Mergeable d, Mergeable e, Mergeable f) => Mergeable (a, b, c, d, e, f) where
  symbolicMerge t (i0, i1, i2, i3, i4, i5) (j0, j1, j2, j3, j4, j5) = (i i0 j0, i i1 j1, i i2 j2, i i3 j3, i i4 j4, i i5 j5)
    where i a b = symbolicMerge t a b
  select xs (err1, err2, err3, err4, err5, err6) ind = (select as err1 ind, select bs err2 ind, select cs err3 ind, select ds err4 ind, select es err5 ind, select fs err6 ind)
    where (as, bs, cs, ds, es, fs) = unzip6 xs

-- 7-Tuple
instance (Mergeable a, Mergeable b, Mergeable c, Mergeable d, Mergeable e, Mergeable f, Mergeable g) => Mergeable (a, b, c, d, e, f, g) where
  symbolicMerge t (i0, i1, i2, i3, i4, i5, i6) (j0, j1, j2, j3, j4, j5, j6) = (i i0 j0, i i1 j1, i i2 j2, i i3 j3, i i4 j4, i i5 j5, i i6 j6)
    where i a b = symbolicMerge t a b
  select xs (err1, err2, err3, err4, err5, err6, err7) ind = (select as err1 ind, select bs err2 ind, select cs err3 ind, select ds err4 ind, select es err5 ind, select fs err6 ind, select gs err7 ind)
    where (as, bs, cs, ds, es, fs, gs) = unzip7 xs

-- Bounded instances
instance (SymWord a, Bounded a) => Bounded (SBV a) where
  minBound = literal minBound
  maxBound = literal maxBound

-- Arrays

-- SArrays are both "EqSymbolic" and "Mergeable"
instance EqSymbolic (SArray a b) where
  (SArray _ a) .== (SArray _ b) = SBV (False, 1) $ Right $ cache c
    where c st = do ai <- uncache a st
                    bi <- uncache b st
                    newExpr st (False, 1) (SBVApp (ArrEq ai bi) [])

instance SymWord b => Mergeable (SArray a b) where
  symbolicMerge = mergeArrays

-- SFunArrays are only "Mergeable". Although a brute
-- force equality can be defined, any non-toy instance
-- will suffer from efficiency issues; so we don't define it
instance SymArray SFunArray where
  newArray _        = newArray_ -- the name is irrelevant in this case
  newArray_  mbiVal = return $ SFunArray $ const $ maybe (error "Reading from an uninitialized array entry") id mbiVal
  readArray  (SFunArray f) a   = f a
  resetArray (SFunArray _) a   = SFunArray $ const a
  writeArray (SFunArray f) a b = SFunArray (\a' -> ite (a .== a') b (f a'))
  mergeArrays t (SFunArray f) (SFunArray g) = SFunArray (\x -> ite t (f x) (g x))

instance SymWord b => Mergeable (SFunArray a b) where
  symbolicMerge = mergeArrays
