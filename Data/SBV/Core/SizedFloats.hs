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

{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Core.SizedFloats (
        -- * Type-sized floats
          FloatingPoint(..), FP(..), FPHalf, FPBFloat, FPSingle, FPDouble, FPQuad

        -- * Constructing values
        , fpFromRawRep, fpFromBigFloat, fpNaN, fpInf, fpZero

        -- * Operations
        , fpFromInteger, fpFromRational, fpFromFloat, fpFromDouble, fpEncodeFloat

        -- * Internal operations
       , fprCompareObject, fprToSMTLib2, mkBFOpts, bfToString, bfRemoveRedundantExp
       ) where

import Data.Char (intToDigit)
import Data.List (isSuffixOf)
import Data.Proxy
import GHC.TypeLits

import Data.Bits
import Data.Ratio
import Numeric

import Data.SBV.Core.Kind
import Data.SBV.Utils.Numeric (floatToWord)

import LibBF (BigFloat, BFOpts, RoundMode, Status)
import qualified LibBF as BF

import qualified Data.Generics as G

-- | A floating point value, indexed by its exponent and significand sizes.
--
--   An IEEE SP is @FloatingPoint  8 24@
--           DP is @FloatingPoint 11 53@
-- etc.
newtype FloatingPoint (eb :: Nat) (sb :: Nat) = FloatingPoint FP
                                              deriving (Eq, Ord)

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
data FP = FP { fpExponentSize    :: Int
             , fpSignificandSize :: Int
             , fpValue           :: BigFloat
             }
             deriving (Ord, Eq, G.Data)

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

-- | Convert from an sign/exponent/mantissa representation to a float. The values are the integers
-- representing the bit-patterns of these values, i.e., the raw representation. We assume that these
-- integers fit into the ranges given, i.e., no overflow checking is done here.
fpFromRawRep :: Bool -> (Integer, Int) -> (Integer, Int) -> FP
fpFromRawRep sign (e, eb) (s, sb) = FP eb sb $ BF.bfFromBits (mkBFOpts eb sb BF.NearEven) val
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

-- | Structural comparison only, for internal map indexes
fprCompareObject :: FP -> FP -> Ordering
fprCompareObject (FP eb sb a) (FP eb' sb' b) = case (eb, sb) `compare` (eb', sb') of
                                                 LT -> LT
                                                 GT -> GT
                                                 EQ -> a `BF.bfCompare` b


-- | Compute the signum of a big float
bfSignum :: BigFloat -> BigFloat
bfSignum r | BF.bfIsNaN  r = r
           | BF.bfIsZero r = r
           | BF.bfIsPos  r = BF.bfFromInteger 1
           | True          = BF.bfFromInteger (-1)

-- | Num instance for big-floats
instance Num FP where
  (+)         = lift2 BF.bfAdd
  (-)         = lift2 BF.bfSub
  (*)         = lift2 BF.bfMul
  abs         = lift1 BF.bfAbs
  signum      = lift1 bfSignum
  fromInteger = error "FP.fromInteger: Not supported for arbitrary floats. Use fpFromInteger instead, specifying the precision"
  negate      = lift1 BF.bfNeg

-- | Fractional instance for big-floats
instance Fractional FP where
  fromRational = error "FP.fromRational: Not supported for arbitrary floats. Use fpFromRational instead, specifying the precision"
  (/)          = lift2 BF.bfDiv

-- | Floating instance for big-floats
instance Floating FP where
  sqrt (FP eb sb a)      = FP eb sb $ fst $ BF.bfSqrt (mkBFOpts eb sb BF.NearEven) a
  FP eb sb a ** FP _ _ b = FP eb sb $ fst $ BF.bfPow  (mkBFOpts eb sb BF.NearEven) a b

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

  isNaN          (FP _ _   r) = BF.bfIsNaN r
  isInfinite     (FP _ _   r) = BF.bfIsInf r
  isDenormalized (FP eb sb r) = BF.bfIsSubnormal (mkBFOpts eb sb BF.NearEven) r
  isNegativeZero (FP _  _  r) = BF.bfIsZero r && BF.bfIsNeg r
  isIEEE         _            = True

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

-- | Real instance for big-floats. Beware, not that well tested!
instance Real FP where
  toRational i
     | n >= 0  = m * 2 ^ n % 1
     | True    = m % 2 ^ abs n
    where (m, n) = decodeFloat i

-- | Real-frac instance for big-floats. Beware, not that well tested!
instance RealFrac FP where
  properFraction (FP eb sb r) = (getInt r', FP eb sb r - FP eb sb r')
       where (r', _)  = BF.bfRoundInt BF.ToNegInf r
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

-- Lift a binary operation. Here we don't call fpFromBigFloat, because the result is correctly rounded.
lift2 :: (BFOpts -> BigFloat -> BigFloat -> (BigFloat, Status)) -> FP -> FP -> FP
lift2 f (FP eb sb a) (FP _ _ b) = FP eb sb $ fst $ f (mkBFOpts eb sb BF.NearEven) a b

-- | Convert from a IEEE float.
fpFromFloat :: Int -> Int -> Float -> FP
fpFromFloat  8 24 f = let fw          = floatToWord f
                          (sgn, e, s) = (fw `testBit` 31, fromIntegral (fw `shiftR` 23) .&. 0xFF, fromIntegral fw .&. 0x7FFFFF)
                      in fpFromRawRep sgn (e, 8) (s, 24)
fpFromFloat eb sb f = error $ "SBV.fprFromFloat: Unexpected input: " ++ show (eb, sb, f)

-- | Convert from a IEEE double.
fpFromDouble :: Int -> Int -> Double -> FP
fpFromDouble 11 53 d = FP 11 54 $ BF.bfFromDouble d
fpFromDouble eb sb d = error $ "SBV.fprFromDouble: Unexpected input: " ++ show (eb, sb, d)
