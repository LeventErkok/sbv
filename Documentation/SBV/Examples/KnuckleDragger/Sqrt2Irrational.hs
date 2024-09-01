-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.Sqrt2Irrational
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Prove that square-root of 2 is irrational.
--
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-unused-matches #-}

module Documentation.SBV.Examples.KnuckleDragger.Sqrt2Irrational where

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

-- | Prove that square-root of @2@ is irrational. If square-root of @2@ is rational, then:
--
--     - There must exist two integers @a@ and @b@ that are co-prime, and @sqrt(2) == a / b@
--     - Thus, @2 == a*a / b*b@
--     - Thus, @a*a == 2*b*b@
--
-- Here's where KnuckleDragger comes in. Let's assume we can prove @a*a == 2*b*b@ implies @a@ and @b@ are
-- both even.
--
-- If above is established, then @a@ and @b@ cannot be co-prime, since they are both even. Thus, there
-- is no ratio @a/b@ that can equal the square-root of 2. This will establish that @2@ must be irrational.
--
-- NB. In fact, one can prove @a*a = 2*b*b@ implies @a@ and @b@ are both @0@, but we won't pursue
-- that fact here. It is not needed to establish our main goal.
--
-- We have:
--
-- >>> sqrt2Irrational
-- Chain: evenSquaredIsEven
--   Lemma: evenSquaredIsEven.1                   Q.E.D.
-- Lemma: evenSquaredIsEven                       Q.E.D.
-- Chain: oddSquaredIsOdd
--   Lemma: oddSquaredIsOdd.1                     Q.E.D.
-- Lemma: oddSquaredIsOdd                         Q.E.D.
-- Chain: evenIfSquareIsEven
--   Lemma: evenIfSquareIsEven.1                  Q.E.D.
-- Lemma: evenIfSquareIsEven                      Q.E.D.
-- Chain: sqrt2_irrational
--   Lemma: sqrt2_irrational.1                    Q.E.D.
--   Lemma: sqrt2_irrational.2                    Q.E.D.
-- Lemma: sqrt2_irrational                        Q.E.D.
sqrt2Irrational :: IO ()
sqrt2Irrational = do
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

    -- Prove that if a square number is even, then its square-root must be even as well
    evenIfSquareIsEven <- chainLemma "evenIfSquareIsEven"
        (\(Forall @"x" x) -> isEven (x * x) .=> isEven x)
        (\x -> [isOdd x, isOdd (x * x)])
        [evenSquaredIsEven, oddSquaredIsOdd]

    -- Prove that square-root of 2 is irrational, by showing for all @a*a == 2*b*b@
    -- implies @a@ and @b@ are both even.
    sqrt2_irrational <- chainLemma "sqrt2_irrational"
        (\(Forall @"a" a) (Forall @"b" b) -> (a*a .== 2*b*b) .=> (isEven a .&& isEven b))
        (\(a :: SInteger) (b :: SInteger) ->
            let c, ca :: SInteger
                c  = a `sDiv` 2
                ca = c * 2
            in [ a*a .== 2*b*b .=> isEven (a*a)
               , isEven (a*a)  .=> isEven a
               , a .== ca      .=> a * a .== 4 * c * c
               ])
        [evenIfSquareIsEven]

    pure ()
