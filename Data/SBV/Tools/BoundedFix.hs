-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.BoundedFix
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bounded fixed-point unrolling.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.BoundedFix (
         bfix
       ) where

import Data.SBV

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV
-- >>> bfac = bfix 10 "fac" fact where fact f n = ite (n .== 0) 1 ((n :: SInteger) * f (n-1))

-- | Bounded fixed-point operation. The call @bfix bnd nm f@ unrolls the recursion in @f@ at most
-- @bnd@ times, and uninterprets the function (with the name @nm@) after the bound is reached.
--
-- This combinator is handy for dealing with recursive definitions that are not symbolically terminating
-- and when the property we are interested in does not require an infinite unrolling, or when we are happy
-- with a bounded proof.  In particular, this operator can be used as a basis of software-bounded model
-- checking algorithms built on top of SBV. The bound can be successively refined in a CEGAR like loop
-- as necessary, by analyzing the counter-examples and rejecting them if they are false-negatives.
--
-- For instance, we can define the factorial function using the bounded fixed-point operator like this:
--
-- @
--     bfac :: SInteger -> SInteger
--     bfac = bfix 10 "fac" fact
--       where fact f n = ite (n .== 0) 1 (n * f (n-1))
-- @
--
-- This definition unrolls the recursion in factorial at most 10 times before uninterpreting the result.
-- We can now prove:
--
-- >>> prove $ \n -> n .>= 1 .&& n .<= 9 .=> bfac n .== n * bfac (n-1)
-- Q.E.D.
--
-- And we would get a bogus counter-example if the proof of our property needs a larger bound:
--
-- >>> prove $ \n -> n .== 10 .=> bfac n .== 3628800
-- Falsifiable. Counter-example:
--   s0 = 10 :: Integer
-- <BLANKLINE>
--   fac :: Integer -> Integer
--   fac _ = 2
--
-- The counter-example is telling us how it instantiated the function @fac@ when the recursion
-- bottomed out: It simply made it return @2@ for all arguments at that point, which provides
-- the (unintended) counter-example.
--
-- By design, if a function defined via `bfix` is given a concrete argument, it will unroll
-- the recursion as much as necessary to complete the call (which can of course diverge). The bound
-- only applies if the given argument is symbolic. This fact can be used to observe concrete
-- values to see where the bounded-model-checking approach fails:
--
-- >>> prove $ \n -> n .== 10 .=> observe "bfac_n" (bfac n) .== observe "bfac_10" (bfac 10)
-- Falsifiable. Counter-example:
--   bfac_10 = 3628800 :: Integer
--   bfac_n  = 7257600 :: Integer
--   s0      =      10 :: Integer
-- <BLANKLINE>
--   fac :: Integer -> Integer
--   fac _ = 2
--
-- Here, we see further evidence that the SMT solver must have decided to assign the
-- value @2@ in the final call just as it was reaching the base case, and thus got the
-- final result incorrect. (Note that @7257600 = 2 * 3628800@.) A wrapper algorithm can
-- then assert the actual value of @bfac 10@ here as an extra constraint and can
-- search for "deeper bugs."
bfix :: (SymVal a, SMTDefinable (SBV a -> r)) => Int -> String -> ((SBV a -> r) -> (SBV a -> r)) -> SBV a -> r
bfix bound nm f x
  | isConcrete x = g x
  | True         = unroll bound x
  where g        = f g
        unroll 0 = uninterpret nm
        unroll i = f (unroll (i-1))
