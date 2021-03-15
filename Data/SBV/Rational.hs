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

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Rational (
    -- * Constructing rationals
      (.%)
  ) where

import qualified Data.Ratio as R

import Data.SBV.Core.Data
import Data.SBV.Core.Model () -- instances only

infixl 7 .%

-- | Construct a symbolic rational from a given numerator and denominator. Note that
-- it is not possible to deconstruct a rational by taking numerator and denominator
-- fields, since we do not represent them canonically. (This is due to the fact that
-- SMTLib has no functions to compute the GCD. One can use the maximization engine
-- to compute the GCD of numbers, but not as a function.)
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
