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
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Core.SizedFloats (
        -- * Type-sized floats
          FloatingPoint(..), FP(..), FPHalf, FPSingle, FPDouble, FPQuad

        -- * Constructing values
        , fpFromRawRep, fpNaN, fpInf, fpZero

        -- * Operations
        , fpFromInteger, fpFromRational, fpFromFloat, fpFromDouble

        -- * Internal operations
       , fprCompareObject, fprToSMTLib2
       ) where

import qualified Data.Numbers.CrackNum as CN (floatToWord)

import Data.Char (intToDigit)
import Data.Proxy
import GHC.TypeLits

import Data.Bits
import Data.Ratio
import Numeric

import Data.SBV.Core.Kind

import LibBF

-- | A floating point value, indexed by its exponent and significand sizes.
--
--   An IEEE SP is @FloatingPoint  8 24@
--           DP is @FloatingPoint 11 53@
-- etc.
newtype FloatingPoint (eb :: Nat) (sb :: Nat) = FloatingPoint FP
                                              deriving (Eq, Ord)

-- | Abbreviation for IEEE half precision float, bit width 16.
type FPHalf = FloatingPoint 5 11

-- | Abbreviation for IEEE single precision float, bit width 32.
type FPSingle = FloatingPoint 8 24

-- | Abbreviation for IEEE double precision float, bit width 64.
type FPDouble = FloatingPoint 11 53

-- | Abbreviation for IEEE quadruble precision float, bit width 128.
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
             deriving (Ord, Eq)

instance Show FP where
  show (FP _ sb r)
    | bfIsNaN  r = "NaN"
    | bfIsInf  r = if bfIsPos r then "Infinity" else "-Infinity"
    | bfIsZero r = if bfIsPos r then "0.0"      else "-0.0"
    | True       = bfToString 10 (addPrefix <> showRnd NearEven <> showFree (Just (fromIntegral sb))) r

-- | Default options for BF options.
defOpts :: Int -> Int -> BFOpts
defOpts eb sb = rnd NearEven <> expBits (fromIntegral eb) <> precBits (fromIntegral sb)

-- | Convert from an sign/exponent/mantissa representation to a float. The values are the integers
-- representing the bit-patterns of these values, i.e., the raw representation. We assume that these
-- integers fit into the ranges given, i.e., no overflow checking is done here.
fpFromRawRep :: Bool -> (Integer, Int) -> (Integer, Int) -> FP
fpFromRawRep sign (e, eb) (s, sb) = FP eb sb $ bfFromBits (defOpts eb sb) val
  where es, val :: Integer
        es = (e `shiftL` (sb - 1)) .|. s
        val | sign = (1 `shiftL` (eb + sb - 1)) .|. es
            | True =                                es

-- | Make NaN. Exponent is all 1s. Significand is non-zero. The sign is irrelevant.
fpNaN :: Int -> Int -> FP
fpNaN eb sb = FP eb sb bfNaN

-- | Make Infinity. Exponent is all 1s. Significand is 0.
fpInf :: Bool -> Int -> Int -> FP
fpInf sign eb sb = FP eb sb (if sign then bfNegInf else bfPosInf)

-- | Make a signed zero.
fpZero :: Bool -> Int -> Int -> FP
fpZero sign eb sb = FP eb sb (if sign then bfNegZero else bfPosZero)

-- | Make from an integer value.
fpFromInteger :: Int -> Int -> Integer -> FP
fpFromInteger eb sb = FP eb sb . bfFromInteger

-- Make a fractional value. We represent all of these in FPRat
fpFromRational :: Int -> Int -> Rational -> FP
fpFromRational eb sb r = FP eb sb $ fst $ bfDiv (defOpts eb sb) top bot
     where FP _ _ top = fpFromInteger eb sb (numerator   r)
           FP _ _ bot = fpFromInteger eb sb (denominator r)

-- | Represent the FP in SMTLib2 format
fprToSMTLib2 :: FP -> String
fprToSMTLib2 (FP eb sb r)
  | bfIsNaN  r = as "NaN"
  | bfIsInf  r = as $ if bfIsPos r then "+oo"   else "-oo"
  | bfIsZero r = as $ if bfIsPos r then "+zero" else "-zero"
  | True       = generic
 where e    = show eb
       s    = show sb

       bits            = bfToBits (defOpts eb sb) r
       significandMask = (1 :: Integer) `shiftL` (sb - 1) - 1
       exponentMask    = (1 :: Integer) `shiftL` eb       - 1

       fpSign          = bits `testBit` (eb + sb - 1)
       fpExponent      = (bits `shiftR` (sb - 1)) .&. exponentMask
       fpSignificand   = bits                     .&. significandMask

       generic = "(fp " ++ unwords [if fpSign then "#b1" else "#b0", mkB eb fpExponent, mkB (sb - 1) fpSignificand] ++ ")"

       as x = "(_ " ++ x ++ " " ++ e ++ " " ++ s ++ ")"

       mkB sz val = "#b" ++ pad sz (showBin val "")
       showBin = showIntAtBase 2 intToDigit
       pad l str = replicate (l - length str) '0' ++ str

-- | Structural comparison only, for internal map indexes
fprCompareObject :: FP -> FP -> Ordering
fprCompareObject (FP eb sb a) (FP eb' sb' b) = case (eb, sb) `compare` (eb', sb') of
                                                 LT -> LT
                                                 GT -> GT
                                                 EQ -> a `bfCompare` b


-- | Compute the signum of a big float
bfSignum :: BigFloat -> BigFloat
bfSignum r | bfIsNaN  r = r
           | bfIsZero r = r
           | bfIsPos  r = bfFromInteger 1
           | True       = bfFromInteger (-1)

-- | Num instance for big-floats
instance Num FP where
  (+)         = lift2 bfAdd
  (*)         = lift2 bfMul
  abs         = lift1 bfAbs
  signum      = lift1 bfSignum
  fromInteger = error "FP.fromInteger: Not supported for arbitrary floats. Use fpFromInteger instead, specifying the precision"
  negate      = lift1 bfNeg

-- | Fractional instance for big-floats
instance Fractional FP where
  fromRational = error "FP.fromRational: Not supported for arbitrary floats. Use fpFromRational instead, specifying the precision"
  (/)          = lift2 bfDiv

instance (KnownNat eb, FPIsAtLeastTwo eb, KnownNat sb, FPIsAtLeastTwo sb) => Num (FloatingPoint eb sb) where
  FloatingPoint (FP eb sb a) + FloatingPoint (FP _ _ b) = FloatingPoint $ FP eb sb $ fst $ bfAdd (defOpts eb sb) a b
  FloatingPoint (FP eb sb a) * FloatingPoint (FP _ _ b) = FloatingPoint $ FP eb sb $ fst $ bfMul (defOpts eb sb) a b

  abs    (FloatingPoint (FP eb sb r)) = FloatingPoint $ FP eb sb $ bfAbs r
  signum (FloatingPoint (FP eb sb r)) = FloatingPoint $ FP eb sb $ bfSignum r
  negate (FloatingPoint (FP eb sb r)) = FloatingPoint $ FP eb sb $ bfNeg r

  fromInteger = FloatingPoint . fpFromInteger (intOfProxy (Proxy @eb)) (intOfProxy (Proxy @sb))

instance (KnownNat eb, FPIsAtLeastTwo eb, KnownNat sb, FPIsAtLeastTwo sb) => Fractional (FloatingPoint eb sb) where
  fromRational = FloatingPoint . fpFromRational (intOfProxy (Proxy @eb)) (intOfProxy (Proxy @sb))

  FloatingPoint (FP eb sb a) / FloatingPoint (FP _ _ b) = FloatingPoint $ FP eb sb (fst (bfDiv (defOpts eb sb) a b))

unsupported :: String -> a
unsupported w = error $ "Data.SBV.FloatingPoint: Unsupported operation: " ++ w ++ ". Please request this as a feature!"

-- Float instance. Most methods are left unimplemented.
instance (KnownNat eb, FPIsAtLeastTwo eb, KnownNat sb, FPIsAtLeastTwo sb) => Floating (FloatingPoint eb sb) where
  pi = fromRational . toRational $ (pi :: Double)
  sqrt (FloatingPoint (FP eb sb a)) = FloatingPoint $ FP eb sb $ fst $ bfSqrt (defOpts eb sb) a

  exp   = unsupported "exp"
  log   = unsupported "log"
  sin   = unsupported "sin"
  cos   = unsupported "cos"
  tan   = unsupported "tan"
  asin  = unsupported "asin"
  acos  = unsupported "acos"
  atan  = unsupported "atan"
  sinh  = unsupported "sinh"
  cosh  = unsupported "cosh"
  tanh  = unsupported "tanh"
  asinh = unsupported "asinh"
  acosh = unsupported "acosh"
  atanh = unsupported "atanh"
  (**)  = unsupported "**"

-- | Lift a unary operation, simple case of function with no status
lift1 :: (BigFloat -> BigFloat) -> FP -> FP
lift1 f (FP eb sb a) = FP eb sb $ f a

-- Lift a binary operation
lift2 :: (BFOpts -> BigFloat -> BigFloat -> (BigFloat, Status)) -> FP -> FP -> FP
lift2 f (FP eb sb a) (FP _ _ b) = FP eb sb $ fst $ f (defOpts eb sb) a b

-- Convert from a IEEE float
fpFromFloat :: Int -> Int -> Float -> FP
fpFromFloat  8 24 f = let fw          = CN.floatToWord f
                          (sgn, e, s) = (fw `testBit` 31, fromIntegral (fw `shiftR` 23) .&. 0xFF, fromIntegral fw .&. 0x7FFFFF)
                      in fpFromRawRep sgn (e, 8) (s, 24)
fpFromFloat eb sb f = error $ "SBV.fprFromFloat: Unexpected input: " ++ show (eb, sb, f)

-- Convert from a IEEE double
fpFromDouble :: Int -> Int -> Double -> FP
fpFromDouble 11 54 d = FP 11 54 $ bfFromDouble d
fpFromDouble eb sb d = error $ "SBV.fprFromDouble: Unexpected input: " ++ show (eb, sb, d)
