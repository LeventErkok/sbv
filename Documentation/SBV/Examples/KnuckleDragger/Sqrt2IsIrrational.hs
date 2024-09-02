-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.Sqrt2IsIrrational
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Prove that square-root of 2 is irrational.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-unused-matches #-}

module Documentation.SBV.Examples.KnuckleDragger.Sqrt2IsIrrational where

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

-- | Prove that square-root of @2@ is irrational. That is, we can never find @a@ and @b@ such that
-- @sqrt 2 == a / b@ and @a@ and @b@ are co-prime.
--
-- In order not to deal with reals and square-roots, we prove the integer-only alternative:
-- If @a^2 = 2b^2@, then @a@ and @b@ cannot be co-prime. We proceed (roughly) as follows:
--
--   (1) Start with @a^2 = 2b^2@.
--   (2) Thus, @a^2@ is even.
--   (3) Thus, @a@ is even.
--   (4) Thus, @a@ is a multiple of @2@, meaning @a^2@ is a multiple of @4@.
--   (5) Thus, @b^2@ must be even.
--   (6) Thus, @b@ is even.
--   (7) Since @a@ and @b@ are both even, they cannot be co-prime.
--
-- Note that KnuckleDragger will fill in most of these gaps, but we'll help it along
-- with several helpers.
--
-- We have:
--
-- >>> sqrt2IsIrrational
-- Chain: evenSquaredIsEven
--   Lemma: evenSquaredIsEven.1                      Q.E.D.
-- Lemma: evenSquaredIsEven                          Q.E.D.
-- Chain: oddSquaredIsOdd
--   Lemma: oddSquaredIsOdd.1                        Q.E.D.
-- Lemma: oddSquaredIsOdd                            Q.E.D.
-- Chain: evenIfSquareIsEven
--   Lemma: evenIfSquareIsEven.1                     Q.E.D.
-- Lemma: evenIfSquareIsEven                         Q.E.D.
-- Chain: sqrt2IsIrrational
--   Lemma: sqrt2IsIrrational.1                      Q.E.D.
-- Theorem: sqrt2IsIrrational                        Q.E.D.
sqrt2IsIrrational :: IO Proven
sqrt2IsIrrational = do
    let isEven :: SInteger -> SBool
        isEven = (2 `sDivides`)

        isOdd :: SInteger -> SBool
        isOdd = sNot . isEven

    -- Prove that an even number squared gives you an even number
    evenSquaredIsEven <- chainLemma "evenSquaredIsEven"
        (\(Forall @"x" x) -> isEven x .=> isEven (x * x))
        (\x -> let h, hx :: SInteger
                   h  = x `sDiv` 2
                   hx = h * 2
               in [x .== hx, hx * hx .== x * x]
        ) []

    -- Prove that an odd number squared gives you an odd number
    oddSquaredIsOdd <- chainLemma "oddSquaredIsOdd"
        (\(Forall @"x" x) -> isOdd x .=> isOdd (x * x))
        (\x -> let h, hx :: SInteger
                   h  = x `sDiv` 2
                   hx = h * 2 + 1
               in [hx .== x, hx * hx .== x * x]
        ) []

    -- Prove that if a number squared is even, then it must be even as well
    evenIfSquareIsEven <- chainLemma "evenIfSquareIsEven"
        (\(Forall @"x" x) -> isEven (x * x) .=> isEven x)
        (\x -> [isOdd x, isOdd (x * x)])
        [evenSquaredIsEven, oddSquaredIsOdd]

    -- Define what it means to be co-prime. Note that we use euclidian notion of modulus here
    -- as z3 deals with that much better. Two numbers are co-prime if for all @z@ that divides both,
    -- @z@ must equal 1.
    let coPrime :: SInteger -> SInteger -> SBool
        coPrime x y = quantifiedBool (\(Forall @"z" z) -> (x `sEMod` z .== 0 .&& y `sEMod` z .== 0) .=> z .== 1)

    -- Prove that square-root of 2 is irrational, by showing for all pairs of integers @a@ and @b@
    -- such that @a*a == 2*b*b@, we can show that @a@ and @b@ are not co-prime:
    chainTheorem "sqrt2IsIrrational"
        (\(Forall @"a" a) (Forall @"b" b) -> ((a*a .== 2*b*b) .=> sNot (coPrime a b)))
        (\(a :: SInteger) (b :: SInteger) ->
             let c = a `sDiv` 2
             in [ isEven (a*a) .=> isEven a
                , a .== 2 * c  .=> a * a .== 4 * c * c
                ])
        [evenIfSquareIsEven]
