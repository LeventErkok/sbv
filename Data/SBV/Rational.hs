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
{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-orphans #-}

module Data.SBV.Rational (
    -- * Constructing rationals
      (.%)
    -- * Rounding rationals
    , sRationalToSIntegerFloor, sRationalToSIntegerCeiling, sRationalToSIntegerTruncate
    , sRationalToSIntegerRoundAway, sRationalToSIntegerRoundToEven, sRationalToSIntegerRM
    -- * Converting between rationals and reals
    , sRationalToSReal, sRealToSRational
    ) where

import qualified Data.Ratio as R

import Data.SBV.Core.AlgReals (isExactRational)
import Data.SBV.Core.Data
import Data.SBV.Core.Model
import Data.SBV.Core.Symbolic (newInternalVariable)
import Data.SBV.Utils.Numeric (roundAway)

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

-- | Convert an SRational to an SInteger, @floor@ version. That is, it computes
-- the largest integer @n@ that satisfies @(n .% 1) <= r@.
--
-- For instance, @1.3@ will be @1@, but @-1.3@ will be @-2@.
--
-- See 'sRationalToSIntegerRM' to select the rounding mode with a symbolic 'SRoundingMode'.
sRationalToSIntegerFloor :: SRational -> SInteger
-- NB: We use @sDiv@ below because it implements division that truncates
-- towards negative infinity, which is exactly what @floor@ needs.
sRationalToSIntegerFloor = lift1 floor (uncurry sDiv)

-- | Convert an SRational to an SInteger, @ceiling@ version. That is, it
-- computes the smallest integer @n@ that satisfies @r <= (n .% 1)@.
--
-- For instance, @1.3@ will be @2@, but @-1.3@ will be @-1@.
--
-- See 'sRationalToSIntegerRM' to select the rounding mode with a symbolic 'SRoundingMode'.
sRationalToSIntegerCeiling :: SRational -> SInteger
sRationalToSIntegerCeiling x
  | Just i <- unliteral x
  = literal $ ceiling i
  | True
  = - (sRationalToSIntegerFloor (- x))

-- | Convert an SRational to an SInteger, truncating version. Truncate simply
-- chops off the fractional part, essentially rounding towards zero.
--
-- For instance, @1.3@ will be @1@, and @-1.3@ will be @-1@.
--
-- See 'sRationalToSIntegerRM' to select the rounding mode with a symbolic 'SRoundingMode'.
sRationalToSIntegerTruncate :: SRational -> SInteger
sRationalToSIntegerTruncate x
  | Just i <- unliteral x
  = literal $ truncate i
  | True
  = ite (x .>= 0) (sRationalToSIntegerFloor x) (sRationalToSIntegerCeiling x)

-- | Convert an SRational to an SInteger by converting to the nearest integer.
-- If there is a tie (i.e., if the fractional component of the SRational is
-- equal to 0.5), then round away from zero.
--
-- For instance:
--
-- * @1.3@ will be @1@
-- * @1.5@ will be @2@ (because @abs 1 < abs 2@)
-- * @1.7@ will be @2@
-- * @2.3@ will be @2@
-- * @2.5@ will be @3@ (because @abs 2 < abs 3@)
-- * @2.7@ will be @3@
-- * @-1.3@ will be @-1@
-- * @-1.5@ will be @-2@ (because @abs (-1) < abs (-2)@)
-- * @-1.7@ will be @-2@
-- * @-2.3@ will be @-2@
-- * @-2.5@ will be @-3@ (because @abs (-2) < abs (-3)@)
-- * @-2.7@ will be @-3@
--
-- See 'sRationalToSIntegerRM' to select the rounding mode with a symbolic 'SRoundingMode'.
sRationalToSIntegerRoundAway :: SRational -> SInteger
sRationalToSIntegerRoundAway x
  | Just i <- unliteral x
  = literal $ roundAway i
  | True
  = ite
      (x .>= 0)
      (sRationalToSIntegerFloor   (x + half))
      (sRationalToSIntegerCeiling (x - half))
  where
    half :: SRational
    half = 0.5

-- | Convert an SRational to an SInteger by converting to the nearest integer.
-- If there is a tie (i.e., if the fractional component of the SRational is
-- equal to 0.5), then round to the nearest even integer.
--
-- For instance:
--
-- * @1.3@ will be @1@
-- * @1.5@ will be @2@ (because @2@ is even)
-- * @1.7@ will be @2@
-- * @2.3@ will be @2@
-- * @2.5@ will be @2@ (because @2@ is even)
-- * @2.7@ will be @3@
-- * @-1.3@ will be @-1@
-- * @-1.5@ will be @-2@ (because @-2@ is even)
-- * @-1.7@ will be @-2@
-- * @-2.3@ will be @-2@
-- * @-2.5@ will be @-2@ (because @-2@ is even)
-- * @-2.7@ will be @-3@
--
-- See 'sRationalToSIntegerRM' to select the rounding mode with a symbolic 'SRoundingMode'.
sRationalToSIntegerRoundToEven :: SRational -> SInteger
sRationalToSIntegerRoundToEven x
  | Just i <- unliteral x
  = literal $ round i
  | True
  = ite (diff .< half) lo $
    ite (diff .> half) hi $
    ite (sDivides 2 lo) lo hi
  where
    half :: SRational
    half = 0.5

    lo, hi :: SInteger
    lo = sRationalToSIntegerFloor x
    hi = lo+1

    diff :: SRational
    diff = x - (lo .% 1)

-- | Convert an 'SRational' to an 'SInteger' according to the supplied
-- 'SRoundingMode'. This dispatches to 'sRationalToSIntegerRoundToEven',
-- 'sRationalToSIntegerRoundAway', 'sRationalToSIntegerCeiling',
-- 'sRationalToSIntegerFloor', and 'sRationalToSIntegerTruncate' for the
-- round-nearest-even, round-nearest-away, round-toward-positive,
-- round-toward-negative, and round-toward-zero modes respectively.
--
-- Note that we re-use the 'SRoundingMode' type here, even though
-- 'SRoundingMode' is normally associated with floating-point operations. The
-- floating-point resemblance is superficial, as this function does not use any
-- floating-point functionality behind the scenes.
sRationalToSIntegerRM :: SRoundingMode -> SRational -> SInteger
sRationalToSIntegerRM rm x =
  sCaseRoundingMode
    (sRationalToSIntegerRoundToEven x)
    (sRationalToSIntegerRoundAway x)
    (sRationalToSIntegerCeiling x)
    (sRationalToSIntegerFloor x)
    (sRationalToSIntegerTruncate x)
    rm

-- | Convert an 'SRational' to an 'SReal'. This conversion is always exact: the
-- rational @t .% b@ maps to the real @t \/ b@. (Recall that denominators are
-- always positive, so no division-by-zero can arise here.)
sRationalToSReal :: SRational -> SReal
sRationalToSReal = lift1 fromRational (\(t, b) -> sFromIntegral t / sFromIntegral b)

-- | Convert an 'SReal' to an 'SRational'. The conversion is /exact/ for reals
-- that are rational: a concrete rational is converted directly, while a
-- symbolic (or non-literal) real is handled by introducing a fresh symbolic
-- rational @r@ and constraining @'sRationalToSReal' r '.==' x@. Thus, whenever
-- the input real is representable as the ratio of two integers, the result
-- denotes exactly that same value---no precision is lost.
--
-- Note the caveat implied by this encoding: if the input real is /irrational/
-- (i.e., not expressible as a ratio of two integers), then the introduced
-- equality constraint is unsatisfiable, which renders the entire problem
-- @UNSAT@. In other words, using this function is an implicit assertion that
-- its argument is a rational number.
sRealToSRational :: SReal -> SRational
sRealToSRational x
  | Just v <- unliteral x, isExactRational v
  = literal (toRational v)
  | True
  = SBV $ SVal KRational $ Right $ cache res
  where res st = do n <- newInternalVariable st KRational
                    let r = SBV (SVal KRational (Right (cache (const (pure n))))) :: SRational
                    internalConstraint st False [] $ unSBV $ sRationalToSReal r .== x
                    pure n

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

-- | Fractional instance for SRational. Just like the 'Num' instance, division is
-- implemented at the SBV level via cross-multiplication, since SMTLib has no direct
-- support for our rational representation. Note that we keep the denominator positive:
-- dividing by @t2 .% b2@ multiplies the denominator by @t2@, which may be negative, so
-- we flip the signs of both parts when needed. Following the SBV convention for reals,
-- division by zero is defined to be zero.
--
-- We mark this @OVERLAPPING@ as it takes precedence over the generic instance in "Data.SBV.Core.Model",
-- which would otherwise try to translate rational division as an SMTLib @Quot@ (which doesn't exist for our rationals).
instance {-# OVERLAPPING #-} Fractional SRational where
  fromRational = literal . fromRational
  a / b        = ite (b .== 0) 0 (lift2 (/) divRat a b)
    where divRat (t1, b1) (t2, b2) = ite (t2 .> 0) (        num .%         den)
                                                   (negate  num .% negate  den)
             where num = t1 * b2
                   den = b1 * t2

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
