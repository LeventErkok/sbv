-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Rational
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Symbolic rationals, corresponds to Haskell's 'Rational' type
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-orphans #-}

module Data.SBV.Rational (
    -- * Constructing rationals
      (.%)
  ) where

import qualified Data.Ratio as R

import Data.SBV.Core.Data
import Data.SBV.Core.Model

infixl 7 .%

-- | Construct a symbolic rational from a given numerator and denominator. Note that
-- it is not possible to deconstruct a rational by taking numerator and denominator
-- fields, since we do not represent them canonically. (This is due to the fact that
-- SMTLib has no functions to compute the GCD. While we can define a recursive function
-- to do so, it would almost always imply non-decidability for even the simplest queries.)
(.%) :: SInteger -> SInteger -> SRational
top .% bot
 | Just t <- unliteral top
 , Just b <- unliteral bot
 = literal $ t R.% b
 | True
 = SBV $ SVal KRational $ Right $ cache res
 where res st = do t <- sbvToSV st top
                   b <- sbvToSV st bot
                   newExpr st KRational $ SBVApp RationalConstructor [t, b]

-- | Get the numerator. Note that this is always symbolic since we don't have a concrete representation.
-- Furthermore this is only used internally and is not exported to the user, since it is not canonical.
doNotExport_numerator :: SRational -> SInteger
doNotExport_numerator x = SBV $ SVal KUnbounded $ Right $ cache res
  where res st = do xv <- sbvToSV st x
                    newExpr st KUnbounded $ SBVApp (Uninterpreted "sbv.rat.numerator") [xv]

-- | Get the numerator. Note that this is always symbolic since we don't have a concrete representation.
-- Furthermore this is only used internally and is not exported to the user, since it is not canonical.
doNotExport_denominator :: SRational -> SInteger
doNotExport_denominator x = SBV $ SVal KUnbounded $ Right $ cache res
  where res st = do xv <- sbvToSV st x
                    newExpr st KUnbounded $ SBVApp (Uninterpreted "sbv.rat.denominator") [xv]

-- | Num instance for SRational. Note that denominators are always positive.
instance Num SRational where
  fromInteger i  = SBV $ SVal KRational $ Left $ mkConstCV KRational (fromIntegral i :: Integer)
  (+)            = lift2 (+)    (\(t1, b1) (t2, b2) -> (t1 * b2 + t2 * b1) .% (b1 * b2))
  (-)            = lift2 (-)    (\(t1, b1) (t2, b2) -> (t1 * b2 - t2 * b1) .% (b1 * b2))
  (*)            = lift2 (*)    (\(t1, b1) (t2, b2) -> (t1      * t2     ) .% (b1 * b2))
  abs            = lift1 abs    (\(t, b) -> abs    t .% b)
  negate         = lift1 negate (\(t, b) -> negate t .% b)
  signum a       = ite (a .> 0) 1 $ ite (a .< 0) (-1) 0

-- | Symbolic ordering for SRational. Note that denominators are always positive.
instance OrdSymbolic SRational where
   (.<)  = lift2 (<)  (\(t1, b1) (t2, b2) -> (t1 * b2) .<  (b1 * t2))
   (.<=) = lift2 (<=) (\(t1, b1) (t2, b2) -> (t1 * b2) .<= (b1 * t2))
   (.>)  = lift2 (>)  (\(t1, b1) (t2, b2) -> (t1 * b2) .>  (b1 * t2))
   (.>=) = lift2 (>=) (\(t1, b1) (t2, b2) -> (t1 * b2) .>= (b1 * t2))

-- | Get the top and bottom parts. Internal only; do not export!
doNotExport_getTB :: SRational -> (SInteger, SInteger)
doNotExport_getTB a = (doNotExport_numerator a, doNotExport_denominator a)

-- | Lift a function over one rational
lift1 :: SymVal t => (Rational -> t) -> ((SInteger,  SInteger) -> SBV t) -> SRational -> SBV t
lift1 cf f a
 | Just va <- unliteral a
 = literal (cf va)
 | True
 = f (doNotExport_getTB a)

-- | Lift a function over two rationals
lift2 :: SymVal t => (Rational -> Rational -> t) -> ((SInteger,  SInteger) -> (SInteger,  SInteger) -> SBV t) -> SRational -> SRational -> SBV t
lift2 cf f a b
 | Just va <- unliteral a, Just vb <- unliteral b
 = literal (va `cf` vb)
 | True
 = f (doNotExport_getTB a) (doNotExport_getTB b)

{- HLint ignore type doNotExport_numerator   "Use camelCase" -}
{- HLint ignore type doNotExport_denominator "Use camelCase" -}
{- HLint ignore type doNotExport_getTB       "Use camelCase" -}
