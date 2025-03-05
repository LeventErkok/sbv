-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.Numeric
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Example use of inductive KnuckleDragger proofs, over integers.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.Numeric where

import Prelude hiding (sum, length)

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

-- | Prove that sum of constants @c@ from @0@ to @n@ is @n*c@.
--
-- We have:
--
-- >>> sumConstProof
-- Inductive lemma: sumConst_correct
--   Base: sumConst_correct.Base           Q.E.D.
--   Asms: 1                               Q.E.D.
--   Step: 1                               Q.E.D.
--   Asms: 2                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: sumConst_correct.Step           Q.E.D.
-- [Proven] sumConst_correct
sumConstProof :: IO Proof
sumConstProof = runKD $ do
   let c :: SInteger
       c = uninterpret "c"

       sum :: SInteger -> SInteger
       sum = smtFunction "sum" $ \n -> ite (n .== 0) 0 (c + sum (n - 1))

       spec :: SInteger -> SInteger
       spec n = c * n

   induct "sumConst_correct"
          (\(Forall @"n" n) -> n .>= 0 .=> sum n .== spec n) $
          \ih k -> [k .>= 0] |- sum (k+1)  ?? k .>= 0
                             =: c + sum k  ?? [hprf ih, hyp (k .>= 0)]
                             =: c + spec k
                             =: c + c*k
                             =: c*(k+1)
                             =: spec (k+1)
                             =: qed

-- | Prove that sum of numbers from @0@ to @n@ is @n*(n-1)/2@.
--
-- Note that z3 (as of mid Feb 2025) can't converge on this quickly, but CVC5 does just fine. We have:
--
-- >>> sumProof
-- Inductive lemma: sum_correct
--   Base: sum_correct.Base                Q.E.D.
--   Asms: 1                               Q.E.D.
--   Step: 1                               Q.E.D.
--   Asms: 2                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: sum_correct.Step                Q.E.D.
-- [Proven] sum_correct
sumProof :: IO Proof
sumProof = runKD $ do
   let sum :: SInteger -> SInteger
       sum = smtFunction "sum" $ \n -> ite (n .== 0) 0 (n + sum (n - 1))

       spec :: SInteger -> SInteger
       spec n = (n * (n+1)) `sDiv` 2

       p :: SInteger -> SBool
       p n = sum n .== spec n

   inductWith cvc5 "sum_correct"
          (\(Forall @"n" n) -> n .>= 0 .=> p n) $
          \ih k -> [k .>= 0] |- sum (k+1)    ?? k .>= 0
                             =: k+1 + sum k  ?? [hprf ih, hyp (k .>= 0)]
                             =: k+1 + spec k
                             =: spec (k+1)
                             =: qed

-- | Prove that sum of square of numbers from @0@ to @n@ is @n*(n+1)*(2n+1)/6@.
--
-- Note that z3 (as of mid Feb 2025) can't converge on this quickly, but CVC5 does just fine. We have:
--
-- >>> sumSquareProof
-- Inductive lemma: sumSquare_correct
--   Base: sumSquare_correct.Base          Q.E.D.
--   Asms: 1                               Q.E.D.
--   Step: 1                               Q.E.D.
--   Asms: 2                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: sumSquare_correct.Step          Q.E.D.
-- [Proven] sumSquare_correct
sumSquareProof :: IO Proof
sumSquareProof = runKD $ do
   let sumSquare :: SInteger -> SInteger
       sumSquare = smtFunction "sumSquare" $ \n -> ite (n .== 0) 0 (n * n + sumSquare (n - 1))

       spec :: SInteger -> SInteger
       spec n = (n * (n+1) * (2*n+1)) `sDiv` 6

       p :: SInteger -> SBool
       p n = sumSquare n .== spec n

   inductWith cvc5 "sumSquare_correct"
          (\(Forall @"n" n) -> n .>= 0 .=> p n) $
          \ih k -> [k .>= 0] |- sumSquare (k+1)           ?? k .>= 0
                             =: (k+1)*(k+1) + sumSquare k ?? [hprf ih, hyp (k .>= 0)]
                             =: (k+1)*(k+1) + spec k
                             =: spec (k+1)
                             =: qed

-- | Prove that @11^n - 4^n@ is always divisible by 7.
--
-- NB. As of Feb 2025, z3 struggles with the inductive step in this proof, but cvc5 performs just fine.
--
-- We have:
--
-- >>> elevenMinusFour
-- Lemma: powN                             Q.E.D.
-- Inductive lemma: elevenMinusFour
--   Base: elevenMinusFour.Base            Q.E.D.
--   Step: 1                               Q.E.D.
--   Asms: 2                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Asms: 3                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Asms: 6                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Step: 7                               Q.E.D.
--   Step: 8                               Q.E.D.
--   Step: elevenMinusFour.Step            Q.E.D.
-- [Proven] elevenMinusFour
elevenMinusFour :: IO Proof
elevenMinusFour = runKD $ do
   let pow :: SInteger -> SInteger -> SInteger
       pow = smtFunction "pow" $ \x y -> ite (y .== 0) 1 (x * pow x (y - 1))

       emf :: SInteger -> SBool
       emf n = 7 `sDivides` (11 `pow` n - 4 `pow` n)

   -- helper
   powN <- lemma "powN" (\(Forall @"x" x) (Forall @"n" n) -> n .>= 0 .=> x `pow` (n+1) .== x * x `pow` n) []

   inductWith cvc5 "elevenMinusFour"
          (\(Forall @"n" n) -> n .>= 0 .=> emf n) $
          \ih k -> [k .>= 0]
                |- emf (k+1)
                =: 7 `sDivides` (11 `pow` (k+1) - 4 `pow` (k+1))
                ?? [hyp (k .>= 0), hprf (powN `at` (Inst @"x" (11 :: SInteger), Inst @"n" k))]
                =: 7 `sDivides` (11 * 11 `pow` k - 4 `pow` (k+1))
                ?? [hyp (k .>= 0), hprf (powN `at` (Inst @"x" ( 4 :: SInteger), Inst @"n" k))]
                =: 7 `sDivides` (11 * 11 `pow` k - 4 * 4 `pow` k)
                =: 7 `sDivides` (7 * 11 `pow` k + 4 * 11 `pow` k - 4 * 4 `pow` k)
                =: 7 `sDivides` (7 * 11 `pow` k + 4 * (11 `pow` k - 4 `pow` k))
                ?? [hyp (k .>= 0), hprf ih]
                =: let x = some "x" (\v -> 7*v .== 11 `pow` k - 4 `pow` k)   -- Apply the IH and grab the witness for it
                in 7 `sDivides` (7 * 11 `pow` k + 4 * 7 * x)
                =: 7 `sDivides` (7 * (11 `pow` k + 4 * x))
                =: sTrue
                =: qed
