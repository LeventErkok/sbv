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
          FP(..), FPC
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

instance Num (FP eb sb) where
  (+)         = error "FP.+"
  (*)         = error "FP.*"
  abs         = error "FP.abs"
  signum      = error "FP.signum"
  fromInteger = error "FP.fromInteger"
  negate      = error "FP.negate"
