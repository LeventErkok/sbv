-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Sqrt2IsIrrational
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

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Sqrt2IsIrrational where

import Prelude hiding (even, odd)

import Data.SBV
import Data.SBV.TP

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
--   (4)  Start with the premise @a^2 = 2b^2@.
--   (5)  Thus, @a^2@ must be even. (Since it equals @2b^2@ by 4.)
--   (6)  Thus, @a@ must be even. (Using 2 and 5.)
--   (7)  Thus, @a^2@ must be divisible by @4@. (Using 3 and 6. That is, @2b^2 == 4K@ for some @K@.)
--   (8)  Thus, @b^2@ must be even. (Using 7, and @b^2 = 2K@.)
--   (9)  Thus, @b@ must be even. (Using 2 and 8.)
--   (10) Since @a@ and @b@ are both even, they cannot be co-prime. (Using 6 and 9.)
--
-- Note that our proof is mostly about the first 3 facts above, then z3 and TP fills in the rest.
--
-- We have:
--
-- >>> sqrt2IsIrrational
-- Lemma: oddSquaredIsOdd
--   Step: 1                               Q.E.D.
--   Step: 2 (expand square)               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: squareEvenImpliesEven            Q.E.D.
-- Lemma: evenSquaredIsMult4
--   Step: 1                               Q.E.D.
--   Step: 2 (expand square)               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: sqrt2IsIrrational                Q.E.D.
-- [Proven] sqrt2IsIrrational
sqrt2IsIrrational :: IO Proof
sqrt2IsIrrational = runTP $ do
    let even, odd :: SInteger -> SBool
        even = (2 `sDivides`)
        odd  = sNot . even

        sq :: SInteger -> SInteger
        sq x = x * x

    -- Prove that an odd number squared gives you an odd number.
    -- We need to help the solver by guiding it through how it can
    -- be decomposed as @2k+1@.
    --
    -- Interestingly, the solver doesn't need the analogous theorem that even number
    -- squared is even, possibly because the even/odd definition above is enough for
    -- it to deduce that fact automatically.
    oddSquaredIsOdd <- calc "oddSquaredIsOdd"
                             (\(Forall @"a" a) -> odd a .=> odd (sq a)) $
                             \a -> [odd a] |- sq a
                                           =: let k = some "k" $ \_k -> a .== 2*_k + 1  -- Grab the witness that a is odd
                                           in sq (2 * k + 1)
                                           ?? "expand square"
                                           =: 4*k*k + 4*k + 1
                                           =: qed

    -- Prove that if a perfect square is even, then it be the square of an even number. For z3, the above proof
    -- is enough to establish this.
    squareEvenImpliesEven <- lemma "squareEvenImpliesEven"
                                   (\(Forall @"a" a) -> even (sq a) .=> even a)
                                   [oddSquaredIsOdd]

    -- Prove that if @a@ is an even number, then its square is four times the square of another.
    evenSquaredIsMult4 <- calc "evenSquaredIsMult4"
                               (\(Forall @"a" a) -> even a .=> 4 `sDivides` sq a) $
                               \a -> [even a] |- sq a
                                              =: let k = some "k" $ \_k -> a .== 2*_k -- Grab the witness that a is even
                                              in sq (2 * k)
                                              ?? "expand square"
                                              =: 4*(k*k)
                                              =: qed

    -- Define what it means to be co-prime. Note that we use euclidian notion of modulus here
    -- as z3 deals with that much better. Two numbers are co-prime if 1 is their only common divisor.
    let coPrime :: SInteger -> SInteger -> SBool
        coPrime x y = quantifiedBool (\(Forall @"z" z) -> (x `sEMod` z .== 0 .&& y `sEMod` z .== 0) .=> z .== 1)

    -- Prove that square-root of 2 is irrational. We do this by showing for all pairs of integers @a@ and @b@
    -- such that @a*a == 2*b*b@, it must be the case that @a@ and @b@ are not be co-prime:
    lemma "sqrt2IsIrrational"
        (\(Forall @"a" a) (Forall @"b" b) -> (sq a .== 2 * sq b) .=> sNot (coPrime a b))
        [squareEvenImpliesEven, evenSquaredIsMult4]
