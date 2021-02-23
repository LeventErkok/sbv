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
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Core.SizedFloats (
        -- * Type-sized floats
          FP(..), FPRep(..)
        -- * Constructing values
        , fprReg, fprNaN, fprInf, fprZero
        -- * Operations
        , fprNegate, fprFromInteger, fprAbs, fprFromFloat, fprFromDouble
        -- * Internal operations
       , fprCompareObject, fprToSMTLib2
       ) where

import qualified Data.Numbers.CrackNum as CN (floatToWord, doubleToWord)

import Data.Char (intToDigit)
import Data.Proxy
import GHC.TypeLits

import Data.Bits
import Data.Ratio
import Numeric

import Data.SBV.Core.Kind

-- | A floating point value, indexed by its exponent and significand sizes.
data FP (eb :: Nat) (sb :: Nat) = FP FPRep

-- | We need an Eq/Ord instance for FP, but only to satisfy the hierarchy
-- The definitions themselves are not supported.
instance Eq  (FP eb sb) where
  a == b = error $ "Data.SBV.SizedFloat: Cannot literally check equality of " ++ show (a, b)

instance Ord (FP eb sb) where
  a `compare` b = error $ "Data.SBV.SizedFloat: Cannot literally compare " ++ show (a, b)

instance Show (FP eb sb) where
  show (FP r) = show r

-- | Internal representation of a parameterized float.
-- If we have eb exponent bits, and sb significand bits, then
-- the total number of floats is 2^sb*(2^eb-1) + 3: All exponents
-- except 11..11 is allowed. So we get, 2^eb-1, different
-- combinations, each with a sign, giving us 2^sb*(2^eb-1) totals.
-- Then we have two infinities, and one NaN, adding 3 more.
data FPRep = FPRSES FPSES
           | FPRInt FPInt
           | FPRRat FPRat

-- | Sign, exponent, significand representation
data FPSES = FPSES { fpSign            :: Bool
                   , fpExponentSize    :: Int
                   , fpExponent        :: Integer
                   , fpSignificandSize :: Int
                   , fpSignificand     :: Integer
                   }

-- | Integer conversion representation
data FPInt = FPInt Int Int Integer  -- Exponent size, Significand size, Integer value we converted from

-- | Rational conversion representation
data FPRat = FPRat Int Int Rational -- Exponent size, Significand size, Rational value we converted from

instance Show FPRep where
  show (FPRSES f@FPSES{fpSign})
    | fprIsNaN      f = "NaN"
    | fprIsInfinite f = if fpSign then "-Infinity" else "Infinity"
    | fprIsZero     f = if fpSign then "-0.0"      else "0.0"
    | True            = fprToSMTLib2 RoundNearestTiesToEven (FPRSES f)
  show (FPRInt (FPInt es ss v)) = "fpFromInteger_"  ++ show es ++ "_" ++ show ss ++ " " ++ show v
  show (FPRRat (FPRat es ss v)) = "fpFromRational_" ++ show es ++ "_" ++ show ss ++ " " ++ show v

-- | Convert to an arbitrary float value
fprReg :: Integer -> (Integer, Int) -> (Integer, Int) -> FPRep
fprReg sign (e, es) (s, sb) = FPRSES $ FPSES { fpSign            = sign == 1
                                             , fpExponentSize    = es
                                             , fpExponent        = e
                                             , fpSignificandSize = sb
                                             , fpSignificand     = s
                                             }

-- | Make NaN. Exponent is all 1s. Significand is non-zero. (So, we pick 1.) The sign is irrelevant, we arbitrarily pick False.
fprNaN :: Int -> Int -> FPRep
fprNaN eb sb = FPRSES $ FPSES { fpSign            = False
                              , fpExponentSize    = eb
                              , fpExponent        = 2 ^ (fromIntegral eb :: Integer) - 1
                              , fpSignificandSize = sb
                              , fpSignificand     = 1
                              }

-- | Is this a NaN?
fprIsNaN :: FPSES -> Bool
fprIsNaN FPSES { fpExponentSize, fpExponent, fpSignificand } = fpExponent == 2 ^ (fromIntegral fpExponentSize :: Integer) - 1 && fpSignificand >= 1

-- | Make Infinity. Exponent is all 1s. Significand is 0.
fprInf :: Bool -> Int -> Int -> FPRep
fprInf sign eb sb = FPRSES $ FPSES { fpSign            = sign
                                   , fpExponentSize    = eb
                                   , fpExponent        = 2 ^ (fromIntegral eb :: Integer) - 1
                                   , fpSignificandSize = sb
                                   , fpSignificand     = 0
                                   }

-- | Is this an infinity?
fprIsInfinite :: FPSES -> Bool
fprIsInfinite FPSES { fpExponentSize, fpExponent, fpSignificand } = fpExponent == 2 ^ (fromIntegral fpExponentSize :: Integer) - 1 && fpSignificand == 0

-- | Is this the zero? Note that this recognizes both positive and negative zero.
fprIsZero :: FPSES -> Bool
fprIsZero FPSES { fpExponent, fpSignificand } = fpExponent == 0 && fpSignificand == 0

-- | Make a signed zero.
fprZero :: Bool -> Int -> Int -> FPRep
fprZero sign eb sb = FPRSES $ FPSES { fpSign            = sign
                                    , fpExponentSize    = eb
                                    , fpExponent        = 0
                                    , fpSignificandSize = sb
                                    , fpSignificand     = 0
                                    }

-- | Make from an integer value. We only represent 0, 1, and -1 in SES format. All others in int format.
fprFromInteger :: Int -> Int -> Integer -> FPRep
fprFromInteger eb sb i
  | i `elem` [-1, 0, 1]
  = let (sign, ex) = case i of
                        0 -> (False, 0)                 -- 0    -> sign is false, and exponent is 0
                        _ -> (i < 0, 2^(eb-1)-1)        -- 1/-1 -> sign follows value, and exponent is the bias, i.e., 2^(eb-1)-1
    in FPRSES $ FPSES { fpSign            = sign
                      , fpExponentSize    = eb
                      , fpExponent        = ex
                      , fpSignificandSize = sb
                      , fpSignificand     = 0
                      }
  | True
  = FPRInt $ FPInt eb sb i

-- Make a fractional value. We represent all of these in FPRat
fprFromRational :: Int -> Int -> Rational -> FPRep
fprFromRational eb sb = FPRRat . FPRat eb sb

-- | Represent the FP in SMTLib2 format
fprToSMTLib2 :: RoundingMode -> FPRep -> String
fprToSMTLib2 _ (FPRSES f@FPSES {fpSign, fpExponentSize, fpExponent, fpSignificandSize, fpSignificand})
 | fprIsNaN f      = as "NaN"
 | fprIsInfinite f = as $ if fpSign then "-oo"   else "+oo"
 | fprIsZero f     = as $ if fpSign then "-zero" else "+zero"
 | True            = generic
 where e = show fpExponentSize
       s = show fpSignificandSize

       generic = "(fp " ++ unwords [if fpSign then "#b1" else "#b0", mkB fpExponentSize fpExponent, mkB (fpSignificandSize - 1) fpSignificand] ++ ")"

       as x = "(_ " ++ x ++ " " ++ e ++ " " ++ s ++ ")"

       mkB sz val = "#b" ++ pad sz (showBin val "")
       showBin = showIntAtBase 2 intToDigit
       pad l str = replicate (l - length str) '0' ++ str
fprToSMTLib2 rm (FPRInt (FPInt fpExponentSize fpSignificandSize intVal))
  = "((_ to_fp " ++ show fpExponentSize ++ " " ++ show fpSignificandSize ++ ") " ++ smtRoundingMode rm ++ " " ++ iv intVal ++ ")"
  where iv x | x >= 0 = "(/ " ++ show x ++ ".0 1.0)"
             | True   = "(- " ++ iv (abs x) ++ ")"
fprToSMTLib2 rm (FPRRat (FPRat fpExponentSize fpSignificandSize ratVal))
  = "((_ to_fp " ++ show fpExponentSize ++ " " ++ show fpSignificandSize ++ ") " ++ smtRoundingMode rm ++ " " ++ iv ratVal ++ ")"
  where iv x | x >= 0 = "(/ " ++ show (numerator x) ++ ".0 " ++ show (denominator x) ++ ".0)"
             | True   = "(- " ++ iv (abs x) ++ ")"

-- | Structural comparison only, for internal map indexes
fprCompareObject :: FPRep -> FPRep -> Ordering
fprCompareObject fpa fpb = case (fpa, fpb) of
                             (FPRSES a, FPRSES b) -> a `compareSES` b
                             (FPRSES{}, FPRInt{}) -> LT
                             (FPRSES{}, FPRRat{}) -> LT

                             (FPRInt{}, FPRSES{}) -> GT
                             (FPRInt a, FPRInt b) -> a `compareInt` b
                             (FPRInt{}, FPRRat{}) -> LT

                             (FPRRat{}, FPRSES{}) -> GT
                             (FPRRat{}, FPRInt{}) -> GT
                             (FPRRat a, FPRRat b) -> a `compareRat` b


  where compareSES (FPSES s es ev ss sv) (FPSES s' es' ev' ss' sv') = (s, es, ev, ss, sv) `compare` (s', es', ev', ss', sv')
        compareInt (FPInt   es    ss  v) (FPInt    es'     ss'  v') = (   es,     ss,  v) `compare` (    es',      ss',  v')
        compareRat (FPRat   es    ss  v) (FPRat    es'     ss'  v') = (   es,     ss,  v) `compare` (    es',      ss',  v')


instance (KnownNat eb, FPIsAtLeastTwo eb, KnownNat sb, FPIsAtLeastTwo sb) => Num (FP eb sb) where
  (+)           = error "FP-TODO: +"
  (*)           = error "FP-TODO: *"
  abs (FP r)    = FP (fprAbs r)
  signum (FP r) = FP (fprSignum r)
  fromInteger   = FP . fprFromInteger (intOfProxy (Proxy @eb)) (intOfProxy (Proxy @sb))
  negate (FP r) = FP (fprNegate r)

instance (KnownNat eb, FPIsAtLeastTwo eb, KnownNat sb, FPIsAtLeastTwo sb) => Fractional (FP eb sb) where
  fromRational = FP . fprFromRational (intOfProxy (Proxy @eb)) (intOfProxy (Proxy @sb))
  (/)          = error "FP-TODO: /"

-- An almost redundant Floating instance. This is so that we can have
-- definitions of nan/infinity etc. work. And one day, may be we can actually
-- do support these as things improve both in SMT-land, and arbitrary precision
-- floats in Haskell
instance (KnownNat eb, FPIsAtLeastTwo eb, KnownNat sb, FPIsAtLeastTwo sb) => Floating (FP eb sb) where
  pi      = fromRational . toRational $ (pi :: Double)
  exp     = error "Data.SBV.FP: exp   is currently not supported. Please request this as a feature!"
  log     = error "Data.SBV.FP: log   is currently not supported. Please request this as a feature!"
  sqrt    = error "Data.SBV.FP: sqrt  is currently not supported. Please request this as a feature!"
  sin     = error "Data.SBV.FP: sin   is currently not supported. Please request this as a feature!"
  cos     = error "Data.SBV.FP: cos   is currently not supported. Please request this as a feature!"
  tan     = error "Data.SBV.FP: tan   is currently not supported. Please request this as a feature!"
  asin    = error "Data.SBV.FP: asin  is currently not supported. Please request this as a feature!"
  acos    = error "Data.SBV.FP: acos  is currently not supported. Please request this as a feature!"
  atan    = error "Data.SBV.FP: atan  is currently not supported. Please request this as a feature!"
  sinh    = error "Data.SBV.FP: sinh  is currently not supported. Please request this as a feature!"
  cosh    = error "Data.SBV.FP: cosh  is currently not supported. Please request this as a feature!"
  tanh    = error "Data.SBV.FP: tanh  is currently not supported. Please request this as a feature!"
  asinh   = error "Data.SBV.FP: asinh is currently not supported. Please request this as a feature!"
  acosh   = error "Data.SBV.FP: acosh is currently not supported. Please request this as a feature!"
  atanh   = error "Data.SBV.FP: atanh is currently not supported. Please request this as a feature!"
  (**)    = error "Data.SBV.FP: **    is currently not supported. Please request this as a feature!"

-- | Negate an arbitrary sized float
fprNegate :: FPRep -> FPRep
fprNegate i@(FPRSES f@FPSES{fpSign})
  | fprIsNaN f = i
  | True       = FPRSES f{fpSign = not fpSign}
fprNegate (FPRInt (FPInt eb sb v)) = FPRInt $ FPInt eb sb (-v)
fprNegate (FPRRat (FPRat eb sb v)) = FPRRat $ FPRat eb sb (-v)

-- | Compute the absolute value of an arbitrary sized float
fprAbs :: FPRep -> FPRep
fprAbs i@(FPRSES f)
  | fprIsNaN f = i
  | True       = FPRSES f{fpSign = False}
fprAbs (FPRInt (FPInt eb sb v)) = FPRInt $ FPInt eb sb (abs v)
fprAbs (FPRRat (FPRat eb sb v)) = FPRRat $ FPRat eb sb (abs v)

-- | Compute the signum of an arbitrary sized float
fprSignum :: FPRep -> FPRep
fprSignum i@(FPRSES f@FPSES{fpSign, fpExponentSize, fpSignificandSize})
  | fprIsNaN f  = i
  | fprIsZero f = i
  | True        = fprFromInteger fpExponentSize fpSignificandSize (if fpSign then 1 else -1)
fprSignum (FPRInt (FPInt eb sb v)) = FPRInt $ FPInt eb sb (signum v)
fprSignum (FPRRat (FPRat eb sb v)) = FPRRat $ FPRat eb sb (signum v)

fprFromFloat :: Int -> Int -> Float -> FPRep
fprFromFloat  8 24 f = let fw          = CN.floatToWord f
                           (sgn, e, s) = (fw `testBit` 31, fromIntegral (fw `shiftR` 23) .&. 0xFF, fromIntegral fw .&. 0x7FFFFF)
                       in FPRSES $ FPSES { fpSign = sgn, fpExponentSize = 8, fpExponent = e, fpSignificandSize = 24, fpSignificand = s }
fprFromFloat eb sb f = error $ "SBV.fprFromFloat: Unexpected input: " ++ show (eb, sb, f)

fprFromDouble :: Int -> Int -> Double -> FPRep
fprFromDouble 11 54 d = let dw          = CN.doubleToWord d
                            (sgn, e, s) = (dw `testBit` 63, fromIntegral (dw `shiftR` 53) .&. 0x7FF, fromIntegral dw .&. 0x1FFFFFFFFFFFFF)
                        in FPRSES $ FPSES { fpSign = sgn, fpExponentSize = 11, fpExponent = e, fpSignificandSize = 54, fpSignificand = s }
fprFromDouble eb sb d = error $ "SBV.fprFromDouble: Unexpected input: " ++ show (eb, sb, d)
