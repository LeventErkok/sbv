-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.AlgReals
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Algrebraic reals in Haskell.
-----------------------------------------------------------------------------

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.SBV.BitVectors.AlgReals (AlgReal, algRealToSMTLib2, algRealToHaskell) where

import Data.List
import Data.Ratio
import System.Random

-- | Algebraic reals. Note that the representation is left abstract. In particular,
-- we only represent explicit rationals on the Haskell side, while we uninterpret
-- roots of polynomials, relying on the backend solver for precise representation.
data AlgReal = AlgRational Rational
             | AlgPolyRoot              -- currently uninterpreted

instance Show AlgReal where
  show (AlgRational a) = showExact a
  show AlgPolyRoot     = "<AlgPolyRoot>"

-- The idea in the instances below is that we will fully support operations
-- on "AlgRational" AlgReals, but leave everything else undefined. When we are
-- on the Haskell side, the AlgReal's are *not* reachable. They only represent
-- return values from SMT solvers, which we should *not* need to manipulate.
instance Eq AlgReal where
  AlgRational a == AlgRational b = a == b
  _             == _             = error "AlgReal.==: unsupported AlgPolyRoot argument"

instance Ord AlgReal where
  AlgRational a `compare` AlgRational b = a `compare` b
  _             `compare` _             = error "AlgReal.compare: unsupported AlgPolyRoot arguments"

instance Num AlgReal where
  AlgRational a + AlgRational b = AlgRational $ a + b
  _             + _             = error "AlgReal.+: unsupported AlgPolyRoot arguments"
  AlgRational a * AlgRational b = AlgRational $ a * b
  _             * _             = error "AlgReal.*: unsupported AlgPolyRoot arguments"
  AlgRational a - AlgRational b = AlgRational $ a - b
  _             - _             = error "AlgReal.-: unsupported AlgPolyRoot arguments"
  abs (AlgRational a)           = AlgRational (abs a)
  abs AlgPolyRoot               = error "AlgReal.abs: unsupported AlgPolyRoot arguments"
  signum (AlgRational a)        = AlgRational (signum a)
  signum AlgPolyRoot            = error "AlgReal.signum: unsupported AlgPolyRoot argument"
  fromInteger a                 = AlgRational (fromInteger a)

instance Fractional AlgReal where
  AlgRational a / AlgRational b = AlgRational (a/b)
  _             / _             = error "AlgReal./: unsupported AlgPolyRoot arguments"
  fromRational                  = AlgRational

instance Random Rational where
  random g = let (a, g')  = random g
                 (b, g'') = random g'
             in (a % b, g'')
  -- this may not be quite kosher, but will do for our purposes (test-generation, mainly)
  randomR (l, h) g = let (ln, ld) = (numerator l, denominator l)
                         (hn, hd) = (numerator h, denominator h)
                         (a, g')  = randomR (ln*hd, hn*ld) g
                     in (a % (ld * hd), g')

instance Random AlgReal where
  random g = let (a, g') = random g in (AlgRational a, g')
  randomR (AlgRational l, AlgRational h) g = let (a, g') = randomR (l, h) g in (AlgRational a, g')
  randomR _                              _ = error "AlgReal.randomR: unsupported AlgPolyRoot bounds"

-- | Render an 'AlgReal' as an SMTLib2 value. Only supports rationals for the time being.
algRealToSMTLib2 :: AlgReal -> String
algRealToSMTLib2 (AlgRational r)
   | m == 0 = "0.0"
   | m < 0  = "(- (/ "  ++ show (abs m) ++ ".0 " ++ show n ++ ".0))"
   | True   =    "(/ "  ++ show m       ++ ".0 " ++ show n ++ ".0)"
  where (m, n) = (numerator r, denominator r)
algRealToSMTLib2 AlgPolyRoot = error "SBV.algRealToSMTLib2: TBD: AlgPolyRoot"

-- | Render an 'AlgReal' as a Haskell value. Only supports rationals, since there is no corresponding
-- standard Haskell type that can represent root-of-polynomial variety.
algRealToHaskell :: AlgReal -> String
algRealToHaskell (AlgRational r) = "((" ++ show r ++ ") :: Rational)"
algRealToHaskell AlgPolyRoot     = error "SBV.algRealToHaskell: Unsupported AlgPolyRoot argument"

-- Try to show a rational precisely if we can, with finite number of
-- digits. Otherwise, show it as a rational value.
showExact :: Rational -> String
showExact r = case f25 (denominator r) [] of
                Nothing               -> show r   -- bail out, not precisely representable with finite digits
                Just (noOfZeros, num) -> let present = length num
                                         in neg $ case noOfZeros `compare` present of
                                                         LT -> let (b, a) = splitAt (present - noOfZeros) num in b ++ "." ++ if null a then "0" else a
                                                         EQ -> "0." ++ num
                                                         GT -> "0." ++ replicate (noOfZeros - present) '0' ++ num
  where neg = if r < 0 then ('-':) else id
        -- factor a number in 2's and 5's if possible
        -- If so, it'll return the number of digits after the zero
        -- to reach the next power of 10, and the numerator value scaled
        -- appropriately and shown as a string
        f25 :: Integer -> [Integer] -> Maybe (Int, String)
        f25 1 sofar = let (ts, fs)   = partition (== 2) sofar
                          [lts, lfs] = map length [ts, fs]
                          noOfZeros  = lts `max` lfs
                      in Just (noOfZeros, show (abs (numerator r)  * factor ts fs))
        f25 v sofar = let (q2, r2) = v `quotRem` 2
                          (q5, r5) = v `quotRem` 5
                      in case (r2, r5) of
                           (0, _) -> f25 q2 (2 : sofar)
                           (_, 0) -> f25 q5 (5 : sofar)
                           _      -> Nothing
        -- compute the next power of 10 we need to get to
        factor []     fs     = product [2 | _ <- fs]
        factor ts     []     = product [5 | _ <- ts]
        factor (_:ts) (_:fs) = factor ts fs
