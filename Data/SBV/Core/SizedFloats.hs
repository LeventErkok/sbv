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
          FP(..), FPRep(..), fprReg, fprNaN, fprInf, fprZero, fprToSMTLib2
       ) where

import Data.Char (intToDigit)
import Data.Proxy
import GHC.TypeLits

import Numeric

import Data.SBV.Core.Kind

-- | A floating point value, indexed by its exponent and significand sizes.
data FP (eb :: Nat) (sb :: Nat) = FP FPRep
                                deriving (Eq, Ord)

instance Show (FP eb sb) where
  show (FP r) = show r

data FPRep = FPRep { fpSign            :: Bool
                   , fpExponentSize    :: Int
                   , fpExponent        :: Integer
                   , fpSignificandSize :: Int
                   , fpSignificand     :: Integer
                   }
                   deriving (Eq, Ord)

instance Show FPRep where
  show f@FPRep{fpSign}
    | fprIsNaN      f = "NaN"
    | fprIsInfinite f = if fpSign then "-Infinity" else "Infinity"
    | fprIsZero     f = if fpSign then "-0.0"      else "0.0"
    | True            = fprToSMTLib2 f

-- | Convert to an arbitrary float value
fprReg :: Integer -> (Integer, Int) -> (Integer, Int) -> FPRep
fprReg sign (e, es) (s, sb) = FPRep { fpSign            = sign == 1
                                    , fpExponentSize    = es
                                    , fpExponent        = e
                                    , fpSignificandSize = sb
                                    , fpSignificand     = s
                                    }

-- | Make NaN. Exponent is all 1s. Significand is 1.
fprNaN :: Int -> Int -> FPRep
fprNaN eb sb = FPRep { fpSign            = False
                     , fpExponentSize    = eb
                     , fpExponent        = 2 ^ (fromIntegral eb :: Integer) - 1
                     , fpSignificandSize = sb
                     , fpSignificand     = 1
                     }

-- | Is this a NaN?
fprIsNaN :: FPRep -> Bool
fprIsNaN FPRep { fpExponentSize, fpExponent, fpSignificand } = fpExponent == 2 ^ (fromIntegral fpExponentSize :: Integer) - 1 && fpSignificand == 1

-- | Make Infinity. Exponent is all 1s. Significand is 0.
fprInf :: Bool -> Int -> Int -> FPRep
fprInf sign eb sb = FPRep { fpSign            = sign
                          , fpExponentSize    = eb
                          , fpExponent        = 2 ^ (fromIntegral eb :: Integer) - 1
                          , fpSignificandSize = sb
                          , fpSignificand     = 0
                          }

-- | Is this an infinity?
fprIsInfinite :: FPRep -> Bool
fprIsInfinite FPRep { fpExponentSize, fpExponent, fpSignificand } = fpExponent == 2 ^ (fromIntegral fpExponentSize :: Integer) - 1 && fpSignificand == 0

-- | Is this an infinity?
fprIsZero :: FPRep -> Bool
fprIsZero FPRep { fpExponent, fpSignificand } = fpExponent == 0 && fpSignificand == 0

-- | Make zero.
fprZero :: Bool -> Int -> Int -> FPRep
fprZero sign eb sb = FPRep { fpSign            = sign
                           , fpExponentSize    = eb
                           , fpExponent        = 0
                           , fpSignificandSize = sb
                           , fpSignificand     = 0
                           }

-- | Make from an integer value
fprFromInteger :: Int -> Int -> Integer -> FPRep
fprFromInteger eb sb v = FPRep { fpSign            = v < 0
                               , fpExponentSize    = eb
                               , fpExponent        = ex
                               , fpSignificandSize = sb
                               , fpSignificand     = sig
                               }
  where (ex, sig) = case v of
                      0 -> (0, 0)
                      i -> error $ "FP-TODO: fpFromInteger: " ++ show i

-- | Represent the FP in SMTLib2 format
fprToSMTLib2 :: FPRep -> String
fprToSMTLib2 f@FPRep {fpSign, fpExponentSize, fpExponent, fpSignificandSize, fpSignificand}
 | fprIsNaN f      = as "NaN"
 | fprIsInfinite f = as $ if fpSign then "-oo"   else "+oo"
 | fprIsZero f     = as $ if fpSign then "-zero" else "+zero"
 | True            = "(fp " ++ unwords [if fpSign then "#b1" else "#b0", mkB fpExponentSize fpExponent, mkB fpSignificandSize fpSignificand] ++ ")"
 where e = show fpExponentSize
       s = show fpSignificandSize

       as x = "(_ " ++ x ++ " " ++ e ++ " " ++ s ++ ")"

       mkB sz val = "#b" ++ pad sz (showBin val "")
       showBin = showIntAtBase 2 intToDigit
       pad l str = replicate (l - length s) '0' ++ str

instance (KnownNat eb, IsNonZero eb, KnownNat sb, IsNonZero sb) => Num (FP eb sb) where
  (+)         = error "FP-TODO: +"
  (*)         = error "FP-TODO: *"
  abs         = error "FP-TODO: abs"
  signum      = error "FP-TODO: signum"
  fromInteger = FP . fprFromInteger (intOfProxy (Proxy @eb)) (intOfProxy (Proxy @sb))
  negate      = error "FP-TODO: negate"
