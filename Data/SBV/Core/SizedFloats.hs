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

module Data.SBV.Core.SizedFloats (
        -- * Type-sized floats
          FP(..), FPC, fpcReg, fpcNaN, fpcInf, fpcZero
       ) where

import GHC.TypeLits

-- | A floating point value, indexed by its exponent and significand sizes.
data FP (eb :: Nat) (sb :: Nat) = FP { fpSign          :: Bool
                                     , fpExponentSize  :: Int
                                     , fpExponent      :: Integer
                                     , fpSignificandSz :: Int
                                     , fpSignificand   :: Integer
                                     }
                                     deriving (Eq, Ord, Show)

type FPC = FP 1 1

-- | Convert to an arbitrary float value
fpcReg :: Integer -> (Integer, Int) -> (Integer, Int) -> FPC
fpcReg sign (e, es) (s, sb) = FP { fpSign          = sign == 1
                                 , fpExponentSize  = es
                                 , fpExponent      = e
                                 , fpSignificandSz = sb
                                 , fpSignificand   = s
                                 }

-- | Make NaN of FPC. Exponent is all 1s. Significand is 1.
fpcNaN :: Integer -> Integer -> FPC
fpcNaN eb sb = FP { fpSign           = False
                  , fpExponentSize   = fromIntegral eb
                  , fpExponent       = 2 ^ eb - 1
                  , fpSignificandSz = fromIntegral sb
                  , fpSignificand   = 1
                  }

-- | Make Infinity of FPC. Exponent is all 1s. Significand is 0.
fpcInf :: Bool -> Integer -> Integer -> FPC
fpcInf sign eb sb = FP { fpSign          = sign
                       , fpExponentSize  = fromIntegral eb
                       , fpExponent      = 2 ^ eb - 1
                       , fpSignificandSz = fromIntegral sb
                       , fpSignificand   = 0
                       }

-- | Make zero of FPC
fpcZero :: Bool -> Integer -> Integer -> FPC
fpcZero sign eb sb = FP { fpSign          = sign
                        , fpExponentSize  = fromIntegral eb
                        , fpExponent      = 0
                        , fpSignificandSz = fromIntegral sb
                        , fpSignificand   = 0
                        }


instance Num (FP eb sb) where
  (+)         = error "FP.+"
  (*)         = error "FP.*"
  abs         = error "FP.abs"
  signum      = error "FP.signum"
  fromInteger = error "FP.fromInteger"
  negate      = error "FP.negate"
