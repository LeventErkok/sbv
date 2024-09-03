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
--   (1) An odd number squared can be written as 2*c+1. We will tell the solver what this c is.
--   (2) Hence, An odd number squared is odd as well.
--   (3) If a number is even, then it's square must be a multiple of 4.
--   (3) If a number is even, then it's square must be a multiple of 4.
--   (4) Start with @a^2 = 2b^2@.
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
-- Lemma: oddSquaredAsMul2P1               Q.E.D.
-- Lemma: oddSquaredIsOdd                  Q.E.D.
-- Lemma: evenIfSquareIsEven               Q.E.D.
-- Lemma: evenSquaredIsMult4               Q.E.D.
-- Lemma: sqrt2IsIrrational                Q.E.D.
sqrt2IsIrrational :: IO Proven
sqrt2IsIrrational = do
    let isEven, isOdd :: SInteger -> SBool
        isEven = (2 `sDivides`)
        isOdd  = sNot . isEven

        sq :: SInteger -> SInteger
        sq x = x * x

    -- Prove that an odd number squared gives you an odd number.
    oddSquaredIsOdd <- do
        -- Help the solver by telling it that if x is odd, then its square can be written as
        -- an odd number as well. Note that we state this by providing a witness (instead of
        -- using an equivaent quantified formula), which allows the solver to conclude
        -- the next lemma easily.
        oddSquaredAsMul2P1 <- lemma "oddSquaredAsMul2P1"
            (\(Forall @"x" x) -> isOdd x .=> sq x .== sq (2 * (x `sDiv` 2) + 1))
            []

        lemma "oddSquaredIsOdd"
            (\(Forall @"x" x) -> isOdd x .=> isOdd (sq x))
            [oddSquaredAsMul2P1]

    -- Prove that if a number squared is even, then it must be even as well.
    evenIfSquareIsEven <- lemma "evenIfSquareIsEven"
        (\(Forall @"x" x) -> isEven (sq x) .=> isEven x)
        [oddSquaredIsOdd]

    -- Define what it means to be co-prime. Note that we use euclidian notion of modulus here
    -- as z3 deals with that much better. Two numbers are co-prime if 1 is their only common divisor.
    let coPrime :: SInteger -> SInteger -> SBool
        coPrime x y = quantifiedBool (\(Forall @"z" z) -> (x `sEMod` z .== 0 .&& y `sEMod` z .== 0) .=> z .== 1)

    -- Prove that if a is an even number, then its square four times the square of another.
    evenSquaredIsMult4 <- lemma "evenSquaredIsMult4"
        (\(Forall @"a" a) -> isEven a .=> quantifiedBool (\(Exists @"b" b) -> sq a .== 4 * sq b))
        []

    -- Prove that square-root of 2 is irrational, by showing for all pairs of integers @a@ and @b@
    -- such that @a*a == 2*b*b@, we can show that @a@ and @b@ are not co-prime:
    lemma "sqrt2IsIrrational"
        (\(Forall @"a" a) (Forall @"b" b) -> ((sq a .== 2 * sq b) .=> sNot (coPrime a b)))
        [evenIfSquareIsEven, evenSquaredIsMult4]
