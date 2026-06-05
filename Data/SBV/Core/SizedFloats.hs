-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Core.Sized
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Type-level sized floats.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-orphans #-}

module Data.SBV.Core.SizedFloats (
        -- * Type-sized floats
          FloatingPoint(..), FP(..), FPHalf, FPBFloat, FPSingle, FPDouble, FPQuad

        -- * Constructing values
        , fpFromRawRep, fpFromBigFloat, fpFromBits, fpNaN, fpInf, fpZero

        -- * Operations
        , fpFromInteger, fpFromRational, fpFromFloat, fpFromDouble
        , fpToFloat, fpToDouble
        , fpEncodeFloat
        , fpIsFinite, fpIsInf, fpIsZero, fpIsNaN
        , fpIsNormal, fpIsSubnormal, fpIsNeg, fpIsPos
        , fpNeg, fpAbs, fpSignum
        , fpAdd, fpSub, fpMul, fpDiv, fpPow, fpRem, fpSqrt, fpFMA
        , fpRoundFloat, fpRoundInt
        , fpMax, fpMin

        -- * Internal operations
       , arbFPIsEqualObjectH, arbFPCompareObjectH, fprToSMTLib2, mkBFOpts, bfToString, bfRemoveRedundantExp
       , roundingModeToRoundMode
       ) where

import Data.Char (intToDigit)
import Data.List (isSuffixOf)
import Data.Proxy
import GHC.TypeLits
import GHC.Real

import Data.Bits
import Numeric

import Data.SBV.Core.Kind
import Data.SBV.Utils.Numeric (RoundingMode(..), floatToWord, fp2fp)

import LibBF (BigFloat, BFOpts, RoundMode, Status, BFRep(..), BFNum(..), bfToRep, Sign(Neg))
import qualified LibBF as BF

import qualified Data.Generics as G

import Control.DeepSeq(NFData(..))

import Test.QuickCheck (Arbitrary(..))

-- | A floating point value, indexed by its exponent and significand sizes.
--
--   An IEEE SP is @FloatingPoint  8 24@
--           DP is @FloatingPoint 11 53@
-- etc.
-- NB. Don't derive Ord for this type automatically, see notes below.
newtype FloatingPoint (eb :: Nat) (sb :: Nat) = FloatingPoint FP deriving Eq

-- NB. Refrain from letting GHC derive @>@ and @>=@ and define
-- it ourselves. Why? Because the default definition of @x > y@
-- is @not (x <= y)@. But when one of the arguments is NaN, this does
-- the wrong thing, since NaN doesn't compare to other values. (i.e., the
-- comparison should be always False, but the default will give
-- you the wrong result.)
instance Ord (FloatingPoint eb sb) where
  FloatingPoint f0 <  FloatingPoint f1 = f0 <  f1
  FloatingPoint f0 <= FloatingPoint f1 = f0 <= f1
  f0               >  f1               = f1 <  f0       -- See the note above
  f0               >= f1               = f1 <= f0       -- See the note above

-- | 'Enum' instance for t'FloatingPoint'. Note that Haskell requires
-- float termination conditions to go over @delta/2@. Also, repeated addition
-- is wrong; instead we need to use multiplication to avoid accuracy issues per the report.
instance ValidFloat eb sb => Enum (FloatingPoint eb sb) where
   succ x = x + 1
   pred x = x - 1

   toEnum                      = fromIntegral
   fromEnum (FloatingPoint fp) = fromInteger (truncate fp)

   enumFrom       = numericEnumFrom
   enumFromTo     = numericEnumFromTo
   enumFromThen   = numericEnumFromThen
   enumFromThenTo = numericEnumFromThenTo

-- | Abbreviation for IEEE half precision float, bit width 16 = 5 + 11.
type FPHalf = FloatingPoint 5 11

-- | Abbreviation for brain-float precision float, bit width 16 = 8 + 8.
type FPBFloat = FloatingPoint 8 8

-- | Abbreviation for IEEE single precision float, bit width 32 = 8 + 24.
type FPSingle = FloatingPoint 8 24

-- | Abbreviation for IEEE double precision float, bit width 64 = 11 + 53.
type FPDouble = FloatingPoint 11 53

-- | Abbreviation for IEEE quadruble precision float, bit width 128 = 15 + 113.
type FPQuad = FloatingPoint 15 113

-- | Show instance for Floats. By default we print in base 10, with standard scientific notation.
instance Show (FloatingPoint eb sb) where
  show (FloatingPoint r) = show r

-- | Internal representation of a parameterized float.
--
-- A note on cardinality: If we have eb exponent bits, and sb significand bits,
-- then the total number of floats is 2^sb*(2^eb-1) + 3: All exponents except 11..11
-- is allowed. So we get, 2^eb-1, different combinations, each with a sign, giving
-- us 2^sb*(2^eb-1) totals. Then we have two infinities, and one NaN, adding 3 more.
data FP = FP { fpExponentSize    :: !Int
             , fpSignificandSize :: !Int
             , fpValue           :: BigFloat
             }
             deriving (Eq, G.Data)

-- Not full, but good enough
instance NFData FP where
  rnf (FP e s _) = e `seq` s `seq` ()

instance ValidFloat eb sb => Arbitrary (FloatingPoint eb sb) where
  arbitrary = FloatingPoint . FP (intOfProxy (Proxy @eb)) (intOfProxy (Proxy @sb))  <$> arbitrary

-- | This arbitrary instance is questionable, but seems to work ok. We get an arbitrary double,
-- and just use that. Probably not good enough for real random work, but good enough here.
instance Arbitrary BigFloat where
  arbitrary = BF.bfFromDouble <$> arbitrary

-- Manually implemented instance as GHC generated a non-IEEE 754 compliant instance.
-- Note that we cannot pack the values in a tuple and then compare them as that will
-- also give non-IEEE 754 compilant results.
--
-- NB. Refrain from letting GHC derive @>@ and @>=@ and define
-- it ourselves. Why? Because the default definition of @x > y@
-- is @not (x <= y)@. But when one of the arguments is NaN, this does
-- the wrong thing, since NaN doesn't compare to other values. (i.e., the
-- comparison should be always False, but the default will give
-- you the wrong result.)
instance Ord FP where
  FP eb0 sb0 v0 <  FP eb1 sb1 v1 | (eb0, sb0) /= (eb1, sb1) = error $ "FP.<: comparing FPs with different precision: "  <> show (eb0, sb0) <> show (eb1, sb1)
                                 | True                     = v0 <  v1
  FP eb0 sb0 v0 <= FP eb1 sb1 v1 | (eb0, sb0) /= (eb1, sb1) = error $ "FP.<=: comparing FPs with different precision: " <> show (eb0, sb0) <> show (eb1, sb1)
                                 | True                     = v0 <= v1
  f0 >  f1 = f1 <  f0  -- See note above
  f0 >= f1 = f1 <= f0  -- See note above

instance Show FP where
  show = bfRemoveRedundantExp . bfToString 10 False False

-- | Remove redundant p+0 etc.
bfRemoveRedundantExp :: String -> String
bfRemoveRedundantExp v = walk useless
  where walk []              = v
        walk (s:ss)
         | s `isSuffixOf` v = reverse . drop (length s) . reverse $ v
         | True             = walk ss

        -- these suffixes are useless, drop them
        useless = [c : s ++ "0" | c <- "pe@", s <- ["+", "-", ""]]

-- | Show a big float in the base given.
-- NB. Do not be tempted to use BF.showFreeMin below; it produces arguably correct
-- but very confusing results. See <https://github.com/GaloisInc/cryptol/issues/1089>
-- for a discussion of the issues.
bfToString :: Int -> Bool -> Bool -> FP -> String
bfToString b withPrefix forceExponent (FP _ sb a)
  | BF.bfIsNaN  a = "NaN"
  | BF.bfIsInf  a = if BF.bfIsPos a then "Infinity" else "-Infinity"
  | BF.bfIsZero a = if BF.bfIsPos a then "0.0"      else "-0.0"
  | True
  = trimZeros $ BF.bfToString b opts' a
  where opts  = BF.showRnd BF.NearEven <> BF.showFree (Just (fromIntegral prec))

        -- For base 10, use a larger precision. It's really difficult to "pick"
        -- the correct value here; but 2*sb seems to work ok. Note that even picking
        -- sb is fine: The output isn't incorrect. It's just confusing.
        prec | b == 10 = 2*sb
             | True    = sb

        opts'
          | withPrefix && forceExponent = BF.addPrefix <> BF.forceExp  <> opts
          | withPrefix                  = BF.addPrefix                 <> opts
          | forceExponent               =                 BF.forceExp  <> opts
          | True                        =                                 opts

        -- In base 10, exponent starts with 'e'. Otherwise (2, 8, 16) it starts with 'p'
        expChar = if b == 10 then 'e' else 'p'

        trimZeros s
          | '.' `elem` s = case span (/= expChar) s of
                            (pre, post) -> let pre' = reverse $ case dropWhile (== '0') $ reverse pre of
                                                                  res@('.':_) -> '0' : res
                                                                  res         -> res
                                           in pre' ++ post
          | True         = s

-- | Default options for BF options.
mkBFOpts :: Integral a => a -> a -> RoundMode -> BFOpts
mkBFOpts eb sb rm = BF.allowSubnormal <> BF.rnd rm <> BF.expBits (fromIntegral eb) <> BF.precBits (fromIntegral sb)

-- | Construct a float, by appropriately rounding
fpFromBigFloat :: Int -> Int -> BigFloat -> FP
fpFromBigFloat eb sb r = FP eb sb $ fst $ BF.bfRoundFloat (mkBFOpts eb sb BF.NearEven) r

-- | Convert an integer to a big-float, preserving the bit-correspondence.
fpFromBits :: Int -> Int -> Integer -> FP
fpFromBits eb sb val = FP eb sb $ BF.bfFromBits (mkBFOpts eb sb BF.NearEven) val

-- | Convert from an sign/exponent/mantissa representation to a float. The values are the integers
-- representing the bit-patterns of these values, i.e., the raw representation. We assume that these
-- integers fit into the ranges given, i.e., no overflow checking is done here.
fpFromRawRep :: Bool -> (Integer, Int) -> (Integer, Int) -> FP
fpFromRawRep sign (e, eb) (s, sb) = fpFromBits eb sb val
  where es, val :: Integer
        es = (e `shiftL` (sb - 1)) .|. s
        val | sign = (1 `shiftL` (eb + sb - 1)) .|. es
            | True =                                es

-- | Make NaN. Exponent is all 1s. Significand is non-zero. The sign is irrelevant.
fpNaN :: Int -> Int -> FP
fpNaN eb sb = fpFromBigFloat eb sb BF.bfNaN

-- | Make Infinity. Exponent is all 1s. Significand is 0.
fpInf :: Bool -> Int -> Int -> FP
fpInf sign eb sb = fpFromBigFloat eb sb $ if sign then BF.bfNegInf else BF.bfPosInf

-- | Make a signed zero.
fpZero :: Bool -> Int -> Int -> FP
fpZero sign eb sb = fpFromBigFloat eb sb $ if sign then BF.bfNegZero else BF.bfPosZero

-- | Make from an integer value.
fpFromInteger :: Int -> Int -> Integer -> FP
fpFromInteger eb sb iv = fpFromBigFloat eb sb $ BF.bfFromInteger iv

-- | Make a generalized floating-point value from a 'Rational'.
fpFromRational :: Int -> Int -> Rational -> FP
fpFromRational eb sb r = FP eb sb $ fst $ BF.bfDiv (mkBFOpts eb sb BF.NearEven) (BF.bfFromInteger (numerator r))
                                                                                (BF.bfFromInteger (denominator r))

-- | Represent the FP in SMTLib2 format
fprToSMTLib2 :: FP -> String
fprToSMTLib2 (FP eb sb r)
  | BF.bfIsNaN  r = as "NaN"
  | BF.bfIsInf  r = as $ if BF.bfIsPos r then "+oo"   else "-oo"
  | BF.bfIsZero r = as $ if BF.bfIsPos r then "+zero" else "-zero"
  | True          = generic
 where e = show eb
       s = show sb

       bits            = BF.bfToBits (mkBFOpts eb sb BF.NearEven) r
       significandMask = (1 :: Integer) `shiftL` (sb - 1) - 1
       exponentMask    = (1 :: Integer) `shiftL` eb       - 1

       fpSign          = bits `testBit` (eb + sb - 1)
       fpExponent      = (bits `shiftR` (sb - 1)) .&. exponentMask
       fpSignificand   = bits                     .&. significandMask

       generic = "(fp " ++ unwords [if fpSign then "#b1" else "#b0", mkB eb fpExponent, mkB (sb - 1) fpSignificand] ++ ")"

       as x = "(_ " ++ x ++ " " ++ e ++ " " ++ s ++ ")"

       mkB sz val = "#b" ++ pad sz (showIntAtBase 2 intToDigit val "")
       pad l str = replicate (l - length str) '0' ++ str

-- | Check that two arbitrary floats are the exact same values, i.e., +0/-0 does not
-- compare equal, and NaN's compare equal to themselves
arbFPIsEqualObjectH :: FP -> FP -> Bool
arbFPIsEqualObjectH (FP eb sb a) (FP eb' sb' b) = case (eb, sb) `compare` (eb', sb') of
                                                    LT                                 -> False
                                                    GT                                 -> False
                                                    EQ | BF.bfIsNaN a                  -> BF.bfIsNaN b
                                                       | BF.bfIsZero a && BF.bfIsNeg a -> BF.bfIsZero b && BF.bfIsNeg b
                                                       | BF.bfIsZero a && BF.bfIsPos a -> BF.bfIsZero b && BF.bfIsPos b
                                                       | True                          -> a == b

-- | Ordering for arbitrary floats, avoiding the +0/-0/NaN issues. Note that this is
-- essentially used for indexing into a map, so we need to be total.
--
-- This function uses the bfCompare function provided by the libBF. As per the libBF's documentation,
-- it has the semantics: -0 < 0, NaN == NaN, and NaN is larger than all other numbers.
arbFPCompareObjectH :: FP -> FP -> Ordering
arbFPCompareObjectH (FP eb sb a) (FP eb' sb' b) = case (eb, sb) `compare` (eb', sb') of
                                                    LT -> LT
                                                    GT -> GT
                                                    EQ -> BF.bfCompare a b
-- | Compute the signum of a big float
bfSignum :: BigFloat -> BigFloat
bfSignum r | BF.bfIsNaN  r = r
           | BF.bfIsZero r = r
           | BF.bfIsPos  r = BF.bfFromInteger 1
           | True          = BF.bfFromInteger (-1)

-- | Num instance for big-floats
instance Num FP where
  (+)           = fpAdd RoundNearestTiesToEven
  (-)           = fpSub RoundNearestTiesToEven
  (*)           = fpMul RoundNearestTiesToEven
  abs           = fpAbs
  signum        = fpSignum
  fromInteger i = error $ "FP.fromInteger: Not supported for arbitrary floats. Use fpFromInteger instead, specifying the precision. Called on: " ++ show i
  negate        = fpNeg

-- | Fractional instance for big-floats
instance Fractional FP where
  fromRational = error "FP.fromRational: Not supported for arbitrary floats. Use fpFromRational instead, specifying the precision"
  (/)          = fpDiv RoundNearestTiesToEven

-- | Floating instance for big-floats
instance Floating FP where
  sqrt = fpSqrt RoundNearestTiesToEven
  (**) = fpPow RoundNearestTiesToEven

  pi    = unsupported "Floating.FP.pi"
  exp   = unsupported "Floating.FP.exp"
  log   = unsupported "Floating.FP.log"
  sin   = unsupported "Floating.FP.sin"
  cos   = unsupported "Floating.FP.cos"
  tan   = unsupported "Floating.FP.tan"
  asin  = unsupported "Floating.FP.asin"
  acos  = unsupported "Floating.FP.acos"
  atan  = unsupported "Floating.FP.atan"
  sinh  = unsupported "Floating.FP.sinh"
  cosh  = unsupported "Floating.FP.cosh"
  tanh  = unsupported "Floating.FP.tanh"
  asinh = unsupported "Floating.FP.asinh"
  acosh = unsupported "Floating.FP.acosh"
  atanh = unsupported "Floating.FP.atanh"

-- | Real-float instance for big-floats. Beware! Some of these aren't really all that well tested.
instance RealFloat FP where
  floatRadix     _            = 2
  floatDigits    (FP _  sb _) = sb
  floatRange     (FP eb _  _) = (fromIntegral (-v+3), fromIntegral v)
     where v :: Integer
           v = 2 ^ ((fromIntegral eb :: Integer) - 1)

  isNaN            = fpIsNaN
  isInfinite       = fpIsInf
  isDenormalized   = fpIsSubnormal
  isNegativeZero f = fpIsZero f && fpIsNeg f
  isIEEE         _ = True

  decodeFloat i@(FP _ _ r) = case BF.bfToRep r of
                               BF.BFNaN     -> decodeFloat (0/0 :: Double)
                               BF.BFRep s n -> case n of
                                                BF.Zero    -> (0, 0)
                                                BF.Inf     -> let (_, m) = floatRange i
                                                                  x = (2 :: Integer) ^ toInteger (m+1)
                                                              in (if s == BF.Neg then -x else x, 0)
                                                BF.Num x y -> -- The value here is x * 2^y
                                                               (if s == BF.Neg then -x else x, fromIntegral y)

  encodeFloat = error "FP.encodeFloat: Not supported for arbitrary floats. Use fpEncodeFloat instead, specifying the precision"

-- | Encode from exponent/mantissa form to a float representation. Corresponds to 'encodeFloat' in Haskell.
fpEncodeFloat :: Int -> Int -> Integer -> Int -> FP
fpEncodeFloat eb sb m n | n < 0 = fpFromRational eb sb (m      % n')
                        | True  = fpFromRational eb sb (m * n' % 1)
    where n' :: Integer
          n' = (2 :: Integer) ^ abs (fromIntegral n :: Integer)

-- | Is a big-float finite?
fpIsFinite :: FP -> Bool
fpIsFinite (FP _ _ r) = BF.bfIsFinite r

-- | Is a big-float infinite?
fpIsInf :: FP -> Bool
fpIsInf (FP _ _ r) = BF.bfIsInf r

-- | Is a big-float a zero value?
fpIsZero :: FP -> Bool
fpIsZero (FP _ _ r) = BF.bfIsZero r

-- | Is a big-float a NaN value?
fpIsNaN :: FP -> Bool
fpIsNaN (FP _ _ r) = BF.bfIsNaN r

-- | Is a big-float \"normal\"? That is, is the value not zero, infinite, NaN,
-- or subnormal?
fpIsNormal :: FP -> Bool
fpIsNormal (FP eb sb r) = BF.bfIsNormal (mkBFOpts eb sb BF.NearEven) r

-- | Is a big-float subnormal (i.e., denormalized)?
fpIsSubnormal :: FP -> Bool
fpIsSubnormal (FP eb sb r) = BF.bfIsSubnormal (mkBFOpts eb sb BF.NearEven) r

-- | Is a big-float negative?
fpIsNeg :: FP -> Bool
fpIsNeg (FP _ _ r) = BF.bfIsNeg r

-- | Is a big-float positive?
fpIsPos :: FP -> Bool
fpIsPos (FP _ _ r) = BF.bfIsPos r

-- | Big-float negation.
fpNeg :: FP -> FP
fpNeg = lift1 BF.bfNeg

-- | Big-float absolute value.
fpAbs :: FP -> FP
fpAbs = lift1 BF.bfAbs

-- | Big-float signum.
fpSignum :: FP -> FP
fpSignum = lift1 bfSignum

-- | Big-float addition.
fpAdd :: RoundingMode -> FP -> FP -> FP
fpAdd = liftRM2 BF.bfAdd

-- | Big-float subtraction.
fpSub :: RoundingMode -> FP -> FP -> FP
fpSub = liftRM2 BF.bfSub

-- | Big-float multiplication.
fpMul :: RoundingMode -> FP -> FP -> FP
fpMul = liftRM2 BF.bfMul

-- | Big-float division.
fpDiv :: RoundingMode -> FP -> FP -> FP
fpDiv = liftRM2 BF.bfDiv

-- | Big-float exponentiation.
fpPow :: RoundingMode -> FP -> FP -> FP
fpPow = liftRM2 BF.bfPow

-- | Big-float remainder.
fpRem :: RoundingMode -> FP -> FP -> FP
fpRem = liftRM2 BF.bfRem

-- | Big-float square root.
fpSqrt :: RoundingMode -> FP -> FP
fpSqrt = liftRM1 BF.bfSqrt

-- | Big-float fused-multiply-add (FMA).
fpFMA :: RoundingMode -> FP -> FP -> FP -> FP
fpFMA = liftRM3 BF.bfFMA

-- | Round a big-float to a float of the given exponent and significand sizes
-- using the given rounding mode.
fpRoundFloat :: Int -> Int -> RoundingMode -> FP -> FP
fpRoundFloat eb sb rm (FP _ _ r) = FP eb sb $ fst $ BF.bfRoundFloat (mkBFOpts eb sb (roundingModeToRoundMode rm)) r

-- | Round a big-float to the nearest integer (represented as a big-float with
-- a zero decimal component) using the given rounding mode.
fpRoundInt :: RoundingMode -> FP -> FP
fpRoundInt rm (FP eb sa a) = FP eb sa $ fst $ BF.bfRoundInt (roundingModeToRoundMode rm) a

-- | SMTLib compliant definition for 'Data.SBV.fpMax'. This is very nearly
-- identical to 'Data.SBV.Utils.Numeric.fpMaxH', except that this uses
-- 'fpIsZero' instead of checking for equality against a @0@ literal. (The
-- latter is not supported for t'FP' values as t'FP' does not implement
-- 'fromInteger'.)
fpMax :: FP -> FP -> FP
fpMax x y
   | isNaN x                                  = y
   | isNaN y                                  = x
   | (isN0 x && isP0 y) || (isN0 y && isP0 x) = error "fpMax: Called with alternating-sign 0's. Not supported"
   | x > y                                    = x
   | True                                     = y
   where isN0   = isNegativeZero
         isP0 a = fpIsZero a && not (isN0 a)

-- | SMTLib compliant definition for 'Data.SBV.fpMin'. This is very nearly
-- identical to 'Data.SBV.Utils.Numeric.fpMinH', except that this uses
-- 'fpIsZero' instead of checking for equality against a @0@ literal. (The
-- latter is not supported for t'FP' values as t'FP' does not implement
-- 'fromInteger'.)
fpMin :: FP -> FP -> FP
fpMin x y
   | isNaN x                                  = y
   | isNaN y                                  = x
   | (isN0 x && isP0 y) || (isN0 y && isP0 x) = error "fpMin: Called with alternating-sign 0's. Not supported"
   | x < y                                    = x
   | True                                     = y
   where isN0   = isNegativeZero
         isP0 a = fpIsZero a && not (isN0 a)

-- | Real instance for big-floats. Beware, not that well tested!
instance Real FP where
  toRational i
     | n >= 0  = m * 2 ^ n % 1
     | True    = m % 2 ^ abs n
    where (m, n) = decodeFloat i

-- | Real-frac instance for big-floats. Beware, not that well tested!
instance RealFrac FP where
  properFraction (FP eb sb r) = (getInt r', FP eb sb r - FP eb sb r')
       where (r', _)  = BF.bfRoundInt BF.ToZero r
             getInt x = case BF.bfToRep x of
                          BF.BFNaN     -> error $ "Data.SBV.FloatingPoint.properFraction: Failed to convert: " ++ show (r, x)
                          BF.BFRep s n -> case n of
                                           BF.Zero    -> 0
                                           BF.Inf     -> error $ "Data.SBV.FloatingPoint.properFraction: Failed to convert: " ++ show (r, x)
                                           BF.Num v y -> -- The value here is x * 2^y, and is integer if y >= 0
                                                         let e :: Integer
                                                             e   = 2 ^ (fromIntegral y :: Integer)
                                                             sgn = if s == BF.Neg then ((-1) *) else id
                                                         in if y > 0
                                                            then fromIntegral $ sgn $ v * e
                                                            else fromIntegral $ sgn v

-- | Real instance for FloatingPoint. NB. The methods haven't been subjected to much testing, so beware of any floating-point snafus here.
instance ValidFloat eb sb => Real (FloatingPoint eb sb) where
  toRational (FloatingPoint (FP _ _ r)) = case bfToRep r of
                                            BFNaN     -> toRational (0/0 :: Double)
                                            BFRep s n -> case n of
                                                           Zero    -> 0 % 1
                                                           Inf     -> (if s == Neg then -1 else 1) % 0
                                                           Num x y -> -- The value here is x * 2^y
                                                                      let v :: Integer
                                                                          v   = 2 ^ abs (fromIntegral y :: Integer)
                                                                          sgn = if s == Neg then ((-1) *) else id
                                                                      in if y > 0
                                                                            then sgn $ x * v % 1
                                                                            else sgn $ x % v

-- | RealFrac instance for FloatingPoint. NB. The methods haven't been subjected to much testing, so beware of any floating-point snafus here.
instance ValidFloat eb sb => RealFrac (FloatingPoint eb sb) where
  properFraction (FloatingPoint f) = (a, FloatingPoint b)
     where (a, b) = properFraction f

-- | Num instance for FloatingPoint
instance ValidFloat eb sb => Num (FloatingPoint eb sb) where
  FloatingPoint a + FloatingPoint b = FloatingPoint $ a + b
  FloatingPoint a * FloatingPoint b = FloatingPoint $ a * b

  abs    (FloatingPoint fp) = FloatingPoint (abs    fp)
  signum (FloatingPoint fp) = FloatingPoint (signum fp)
  negate (FloatingPoint fp) = FloatingPoint (negate fp)

  fromInteger = FloatingPoint . fpFromInteger (intOfProxy (Proxy @eb)) (intOfProxy (Proxy @sb))

instance ValidFloat eb sb => Fractional (FloatingPoint eb sb) where
  fromRational = FloatingPoint . fpFromRational (intOfProxy (Proxy @eb)) (intOfProxy (Proxy @sb))

  FloatingPoint a / FloatingPoint b = FloatingPoint (a / b)

unsupported :: String -> a
unsupported w = error $ "Data.SBV.FloatingPoint: Unsupported operation: " ++ w ++ ". Please request this as a feature!"

-- Float instance. Most methods are left unimplemented.
instance ValidFloat eb sb => Floating (FloatingPoint eb sb) where
  pi = FloatingPoint pi

  exp  (FloatingPoint i) = FloatingPoint (exp i)
  sqrt (FloatingPoint i) = FloatingPoint (sqrt i)

  FloatingPoint a ** FloatingPoint b = FloatingPoint $ a ** b

  log   (FloatingPoint i) = FloatingPoint (log   i)
  sin   (FloatingPoint i) = FloatingPoint (sin   i)
  cos   (FloatingPoint i) = FloatingPoint (cos   i)
  tan   (FloatingPoint i) = FloatingPoint (tan   i)
  asin  (FloatingPoint i) = FloatingPoint (asin  i)
  acos  (FloatingPoint i) = FloatingPoint (acos  i)
  atan  (FloatingPoint i) = FloatingPoint (atan  i)
  sinh  (FloatingPoint i) = FloatingPoint (sinh  i)
  cosh  (FloatingPoint i) = FloatingPoint (cosh  i)
  tanh  (FloatingPoint i) = FloatingPoint (tanh  i)
  asinh (FloatingPoint i) = FloatingPoint (asinh i)
  acosh (FloatingPoint i) = FloatingPoint (acosh i)
  atanh (FloatingPoint i) = FloatingPoint (atanh i)

-- | Lift a unary operation, simple case of function with no status. Here, we call fpFromBigFloat since the big-float isn't size aware.
lift1 :: (BigFloat -> BigFloat) -> FP -> FP
lift1 f (FP eb sb a) = fpFromBigFloat eb sb $ f a

-- | Lift a unary operation that returns a big-float and a status.
liftRM1 :: (BFOpts -> BigFloat -> (BigFloat, Status)) -> RoundingMode -> FP -> FP
liftRM1 f rm (FP eb sb a) = FP eb sb $ fst $ f (mkBFOpts eb sb (roundingModeToRoundMode rm)) a

-- | Lift a binary operation that returns a big-float and a status.
liftRM2 :: (BFOpts -> BigFloat -> BigFloat -> (BigFloat, Status)) -> RoundingMode -> FP -> FP -> FP
liftRM2 f rm (FP eb sb a) (FP _ _ b) = FP eb sb $ fst $ f (mkBFOpts eb sb (roundingModeToRoundMode rm)) a b

-- | Lift a trinary operation that returns a big-float and a status.
liftRM3 :: (BFOpts -> BigFloat -> BigFloat -> BigFloat -> (BigFloat, Status)) -> RoundingMode -> FP -> FP -> FP -> FP
liftRM3 f rm (FP eb sb a) (FP _ _ b) (FP _ _ c) = FP eb sb $ fst $ f (mkBFOpts eb sb (roundingModeToRoundMode rm)) a b c

-- | Convert from a IEEE float.
fpFromFloat :: Int -> Int -> Float -> FP
fpFromFloat  8 24 f = let fw          = floatToWord f
                          (sgn, e, s) = (fw `testBit` 31, fromIntegral (fw `shiftR` 23) .&. 0xFF, fromIntegral fw .&. 0x7FFFFF)
                      in fpFromRawRep sgn (e, 8) (s, 24)
fpFromFloat eb sb f = error $ "SBV.fpFromFloat: Unexpected input: " ++ show (eb, sb, f)

-- | Convert from a IEEE double.
fpFromDouble :: Int -> Int -> Double -> FP
fpFromDouble 11 53 d = FP 11 54 $ BF.bfFromDouble d
fpFromDouble eb sb d = error $ "SBV.fpFromDouble: Unexpected input: " ++ show (eb, sb, d)

-- | Convert to a IEEE float using the given rounding mode.
fpToFloat :: RoundingMode -> FP -> Float
fpToFloat rm (FP _ _ r) = fp2fp $ fst $ BF.bfToDouble (roundingModeToRoundMode rm) r

-- | Convert to a IEEE double using the given rounding mode.
fpToDouble :: RoundingMode -> FP -> Double
fpToDouble rm (FP _ _ r) = fst $ BF.bfToDouble (roundingModeToRoundMode rm) r

-- | Map SBV's rounding modes to LibBF's.
roundingModeToRoundMode :: RoundingMode -> RoundMode
roundingModeToRoundMode RoundNearestTiesToEven = BF.NearEven
roundingModeToRoundMode RoundNearestTiesToAway = BF.NearAway
roundingModeToRoundMode RoundTowardPositive    = BF.ToPosInf
roundingModeToRoundMode RoundTowardNegative    = BF.ToNegInf
roundingModeToRoundMode RoundTowardZero        = BF.ToZero
