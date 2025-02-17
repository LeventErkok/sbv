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
-- Lemma: sumConst_correct                 Q.E.D.
-- [Proven] sumConst_correct
sumConstProof :: IO Proof
sumConstProof = runKD $ do
   let c :: SInteger
       c = uninterpret "c"

       sum :: SInteger -> SInteger
       sum = smtFunction "sum" $ \n -> ite (n .== 0) 0 (c + sum (n - 1))

       spec :: SInteger -> SInteger
       spec n = c * n

       p :: SInteger -> SBool
       p n = sum n .== spec n

   induct "sumConst_correct"
          (\(Forall @"n" n) -> n .>= 0 .=> p n) $
          \ih k -> sTrue |- sum (k+1)
                         =: c + sum k  ? ih
                         =: c + spec k
                         =: c + c*k
                         =: c*(k+1)
                         =: spec (k+1)
                         =: qed

-- | Prove that sum of numbers from @0@ to @n@ is @n*(n-1)/2@.
--
-- We have:
--
-- >>> sumProof
-- Inductive lemma: sum_correct
--   Base: sum_correct.Base                Q.E.D.
--   Help: sum_correct.L1 vs L2            Q.E.D.
--   Help: sum_correct.L2 vs R1            Q.E.D.
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

   induct "sum_correct"
          (\(Forall @"n" n) -> n .>= 0 .=> p n) $
          \ih k -> sTrue |- sum (k+1)
                         =: k+1 + sum k  ? ih
                         =: k+1 + spec k
                         =: spec (k+1)
                         =: qed

-- | Prove that sum of square of numbers from @0@ to @n@ is @n*(n+1)*(2n+1)/6@.
--
-- We have:
--
-- >>> sumSquareProof
-- Inductive lemma: sumSquare_correct
--   Base: sumSquare_correct.Base          Q.E.D.
--   Help: sumSquare_correct.L1 vs L2      Q.E.D.
--   Help: sumSquare_correct.L2 vs L3      Q.E.D.
--   Help: sumSquare_correct.L3 vs L4      Q.E.D.
--   Help: sumSquare_correct.L4 vs L5      Q.E.D.
--   Help: sumSquare_correct.L5 vs L6      Q.E.D.
--   Help: sumSquare_correct.L6 vs L7      Q.E.D.
--   Help: sumSquare_correct.R1 vs R2      Q.E.D.
--   Help: sumSquare_correct.L7 vs R2      Q.E.D.
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

   induct "sumSquare_correct"
          (\(Forall @"n" n) -> n .>= 0 .=> p n) $
          \ih k -> sTrue |- sumSquare (k+1)
                         =: (k+1)*(k+1) + sumSquare k ? ih
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
-- Lemma: pow0                             Q.E.D.
-- Lemma: powN                             Q.E.D.
-- Lemma: elevenMinusFour                  Q.E.D.
-- [Proven] elevenMinusFour
elevenMinusFour :: IO Proof
elevenMinusFour = runKD $ do
   let pow :: SInteger -> SInteger -> SInteger
       pow = smtFunction "pow" $ \x y -> ite (y .== 0) 1 (x * pow x (y - 1))

       emf :: SInteger -> SBool
       emf n = 7 `sDivides` (11 `pow` n - 4 `pow` n)

   _ow0 <- lemma "pow0" (\(Forall @"x" x)                 ->             x `pow` 0     .== 1)             []
   powN <- lemma "powN" (\(Forall @"x" x) (Forall @"n" n) -> n .>= 0 .=> x `pow` (n+1) .== x * x `pow` n) []

   inductWith cvc5 "elevenMinusFour"
          (\(Forall @"n" n) -> n .>= 0 .=> emf n) $
          \ih k -> let x = some "x" (\v -> 7 * v .== 11 `pow` k - 4 `pow` k)
                   in sTrue |- emf (k+1)
                            =: 7 `sDivides` (11 `pow` (k+1) - 4 `pow` (k+1))                  ? powN `at` (Inst @"x" (11 :: SInteger), Inst @"n" k)
                            =: 7 `sDivides` (11 * 11 `pow` k - 4 `pow` (k+1))                 ? powN `at` (Inst @"x" ( 4 :: SInteger), Inst @"n" k)
                            =: 7 `sDivides` (11 * 11 `pow` k - 4 * 4 `pow` k)
                            =: 7 `sDivides` (7 * 11 `pow` k + 4 * 11 `pow` k - 4 * 4 `pow` k)
                            =: 7 `sDivides` (7 * 11 `pow` k + 4 * (11 `pow` k - 4 `pow` k))   ? ih
                            =: 7 `sDivides` (7 * 11 `pow` k + 4 * 7 * x)
                            =: 7 `sDivides` (7 * (11 `pow` k + 4 * x))
                            =: sTrue
                            =: qed
