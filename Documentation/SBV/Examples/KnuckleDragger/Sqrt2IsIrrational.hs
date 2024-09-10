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

import Prelude hiding (even, odd)

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV.Tools.KnuckleDragger(runKD)

-- | Prove that square-root of @2@ is irrational. That is, we can never find @a@ and @b@ such that
-- @sqrt 2 == a / b@ and @a@ and @b@ are co-prime.
--
-- In order not to deal with reals and square-roots, we prove the integer-only alternative:
-- If @a^2 = 2b^2@, then @a@ and @b@ cannot be co-prime. We proceed by establishing the
-- following helpers first:
--
--   (1) An odd number squared is odd: @odd x -> odd x^2@
--   (2) An even number that is a perfect square must be the square of an even number: @even x^2 -> even x@.
--   (3) If a number is even, then its square must be a multiple of 4: @even x .=> x*x % 4 == 0@.
--
--  Using these helpers, we can argue:
--
--   (a) Start with the premise @a^2 = 2b^2@.
--   (b) Thus, @a^2@ must be even. (Since it equals @2b^2@ by a.)
--   (c) Thus, @a@ must be even. (Using 2 and b.)
--   (d) Thus, @a^2@ must be divisible by @4@. (Using 3 and c. That is, 2b^2 == 4*K for someK.)
--   (e) Thus, @b^2@ must be even. (Using d, b^2 = 2K.)
--   (f) Thus, @b@ must be even. (Using 2 and e.)
--   (g) Since @a@ and @b@ are both even, they cannot be co-prime. (Using c and f.)
--
-- Note that our proof is mostly about the first 3 facts above, then z3 and KnuckleDragger fills in the rest.
--
-- We have:
--
-- >>> runKD sqrt2IsIrrational
-- Lemma: expandOddXInSq                   Q.E.D.
-- Lemma: oddSquaredIsOdd                  Q.E.D.
-- Lemma: evenIfSquareIsEven               Q.E.D.
-- Lemma: evenSquaredIsMult4               Q.E.D.
-- Lemma: sqrt2IsIrrational                Q.E.D.
sqrt2IsIrrational :: KD Proven
sqrt2IsIrrational = do
    let even, odd :: SInteger -> SBool
        even = (2 `sDivides`)
        odd  = sNot . even

        sq :: SInteger -> SInteger
        sq x = x * x

    -- Prove that an odd number squared gives you an odd number.
    -- Interestingly, the solver doesn't need the analogous theorem that even number
    -- squared is even, possibly because the even/odd definition above is enough for
    -- it to deduce that fact automatically.
    oddSquaredIsOdd <- do

        -- Help the solver by explicitly proving  that if @x@ is odd, then it can be written as @2k+1@.
        -- We do need to do this in a bit of a round about way, proving @sq x@ is the square
        -- of another odd number, as that seems to help z3 do better quantifier instantiation.
        --
        -- Note that, instead of using an existential quantifier for k, we actually tell
        -- the solver what the witness is, which makes the proof go through.
        expandOddXInSq <- lemma "expandOddXInSq"
            (\(Forall @"x" x) -> odd x .=> sq x .== sq (2 * (x `sDiv` 2) + 1))
            []

        lemma "oddSquaredIsOdd"
            (\(Forall @"x" x) -> odd x .=> odd (sq x))
            [expandOddXInSq]

    -- Prove that if a perfect square is even, then it be the square of an even number. For z3, the above proof
    -- is enough to establish this.
    evenIfSquareIsEven <- lemma "evenIfSquareIsEven" (\(Forall @"x" x) -> even (sq x) .=> even x) [oddSquaredIsOdd]

    -- Prove that if @a@ is an even number, then its square is four times the square of another.
    -- Happily, z3 needs no helpers to establish this all on its own.
    evenSquaredIsMult4 <- lemma "evenSquaredIsMult4"
        (\(Forall @"a" a) -> even a .=> quantifiedBool (\(Exists @"b" b) -> sq a .== 4 * sq b))
        []

    -- Define what it means to be co-prime. Note that we use euclidian notion of modulus here
    -- as z3 deals with that much better. Two numbers are co-prime if 1 is their only common divisor.
    let coPrime :: SInteger -> SInteger -> SBool
        coPrime x y = quantifiedBool (\(Forall @"z" z) -> (x `sEMod` z .== 0 .&& y `sEMod` z .== 0) .=> z .== 1)

    -- Prove that square-root of 2 is irrational. We do this by showing for all pairs of integers @a@ and @b@
    -- such that @a*a == 2*b*b@, it must be the case that @a@ and @b@ are not be co-prime:
    lemma "sqrt2IsIrrational"
        (\(Forall @"a" a) (Forall @"b" b) -> ((sq a .== 2 * sq b) .=> sNot (coPrime a b)))
        [evenIfSquareIsEven, evenSquaredIsMult4]
