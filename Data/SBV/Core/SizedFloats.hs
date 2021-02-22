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
          FP(..), FPRep(..), fprReg, fprNaN, fprInf, fprZero
       ) where

import GHC.TypeLits

-- | A floating point value, indexed by its exponent and significand sizes.
data FP (eb :: Nat) (sb :: Nat) = FP FPRep
                                deriving (Eq, Ord, Show)

data FPRep = FPRep { fpSign          :: Bool
                   , fpExponentSize  :: Int
                   , fpExponent      :: Integer
                   , fpSignificandSz :: Int
                   , fpSignificand   :: Integer
                   }
                   deriving (Eq, Ord, Show)

-- | Convert to an arbitrary float value
fprReg :: Integer -> (Integer, Int) -> (Integer, Int) -> FPRep
fprReg sign (e, es) (s, sb) = FPRep { fpSign          = sign == 1
                                    , fpExponentSize  = es
                                    , fpExponent      = e
                                    , fpSignificandSz = sb
                                    , fpSignificand   = s
                                    }

-- | Make NaN. Exponent is all 1s. Significand is 1.
fprNaN :: Int -> Int -> FPRep
fprNaN eb sb = FPRep { fpSign          = False
                     , fpExponentSize  = eb
                     , fpExponent      = 2 ^ (fromIntegral eb :: Integer) - 1
                     , fpSignificandSz = sb
                     , fpSignificand   = 1
                     }

-- | Make Infinity. Exponent is all 1s. Significand is 0.
fprInf :: Bool -> Int -> Int -> FPRep
fprInf sign eb sb = FPRep { fpSign          = sign
                          , fpExponentSize  = eb
                          , fpExponent      = 2 ^ (fromIntegral eb :: Integer) - 1
                          , fpSignificandSz = sb
                          , fpSignificand   = 0
                          }

-- | Make zero.
fprZero :: Bool -> Int -> Int -> FPRep
fprZero sign eb sb = FPRep { fpSign          = sign
                           , fpExponentSize  = eb
                           , fpExponent      = 0
                           , fpSignificandSz = sb
                           , fpSignificand   = 0
                           }

instance Num (FP eb sb) where
  (+)         = error "FP-TODO: +"
  (*)         = error "FP-TODO: *"
  abs         = error "FP-TODO: abs"
  signum      = error "FP-TODO: signum"
  fromInteger = error "FP-TODO: fromInteger"
  negate      = error "FP-TODO: negate"
