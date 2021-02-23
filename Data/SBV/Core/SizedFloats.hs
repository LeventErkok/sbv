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
          FP(..), FPRep(..), fprCompareObject, fprReg, fprNaN, fprInf, fprZero, fprToSMTLib2, fprNegate
       ) where

import Data.Char (intToDigit)
import Data.Proxy
import GHC.TypeLits

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

-- | Sign, exponent, significand representation
data FPSES = FPSES { fpSign            :: Bool
                   , fpExponentSize    :: Int
                   , fpExponent        :: Integer
                   , fpSignificandSize :: Int
                   , fpSignificand     :: Integer
                   }

-- | Integer conversion representation
data FPInt = FPInt Int Int Integer  -- Exponent size, Significand size, Integer value we converted from

instance Show FPRep where
  show (FPRSES f@FPSES{fpSign})
    | fprIsNaN      f = "NaN"
    | fprIsInfinite f = if fpSign then "-Infinity" else "Infinity"
    | fprIsZero     f = if fpSign then "-0.0"      else "0.0"
    | True            = fprToSMTLib2 RoundNearestTiesToEven (FPRSES f)
  show (FPRInt (FPInt es ss v)) = "fpFromInteger_" ++ show es ++ "_" ++ show ss ++ " " ++ show v

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

-- | Make from an integer value. We only represent 0 in SES format. All others in int format.
fprFromInteger :: Int -> Int -> Integer -> FPRep
fprFromInteger eb sb 0 = FPRSES $ FPSES { fpSign            = False
                                        , fpExponentSize    = eb
                                        , fpExponent        = 0
                                        , fpSignificandSize = sb
                                        , fpSignificand     = 0
                                        }
fprFromInteger eb sb i = FPRInt $ FPInt eb sb i

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

-- | Structural comparison only, for internal map indexes
fprCompareObject :: FPRep -> FPRep -> Ordering
fprCompareObject fpa fpb = case (fpa, fpb) of
                             (FPRSES a, FPRSES b) -> a `compareSES` b
                             (FPRSES{}, FPRInt{}) -> LT
                             (FPRInt{}, FPRSES{}) -> GT
                             (FPRInt a, FPRInt b) -> a `compareInt` b
  where compareSES (FPSES s es ev ss sv) (FPSES s' es' ev' ss' sv') = (s, es, ev, ss, sv) `compare` (s', es', ev', ss', sv')
        compareInt (FPInt   es    ss  v) (FPInt    es'     ss'  v') = (   es,     ss,  v) `compare` (    es',      ss',  v')


instance (KnownNat eb, FPIsAtLeastTwo eb, KnownNat sb, FPIsAtLeastTwo sb) => Num (FP eb sb) where
  (+)         = error "FP-TODO: +"
  (*)         = error "FP-TODO: *"
  abs         = error "FP-TODO: abs"
  signum      = error "FP-TODO: signum"
  fromInteger = FP . fprFromInteger (intOfProxy (Proxy @eb)) (intOfProxy (Proxy @sb))
  negate      = error "FP-TODO: negate"

-- Negate an arbitrary sized float
fprNegate :: FPRep -> FPRep
fprNegate i@(FPRSES f@FPSES{fpSign})
  | fprIsNaN f = i
  | True       = FPRSES f{fpSign = not fpSign}
fprNegate (FPRInt (FPInt eb sb v)) = FPRInt $ FPInt eb sb (-v)
