-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.Induction
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Example use of the KnuckleDragger, for some inductive proofs
-----------------------------------------------------------------------------

{-# LANGUAGE CPP              #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeAbstractions #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.Induction where

import Prelude hiding (sum, length)

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

#ifndef HADDOCK
-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV.Tools.KnuckleDragger(runKD)
#endif

-- | Prove that sum of constants @c@ from @0@ to @n@ is @n*c@.
--
-- We have:
--
-- >>> runKD sumConstProof
-- Lemma: sumConst_correct                 Q.E.D.
-- [Proven] sumConst_correct
sumConstProof :: KD Proof
sumConstProof = do
   let sum :: SInteger -> SInteger -> SInteger
       sum = smtFunction "sum" $ \n c -> ite (n .== 0) 0 (c + sum (n-1) c)

       spec :: SInteger -> SInteger -> SInteger
       spec n c = n * c

       p :: SInteger -> SInteger -> SBool
       p n c = observe "imp" (sum n c) .== observe "spec" (spec n c)

   lemma "sumConst_correct" (\(Forall @"n" n) (Forall @"c" c) -> n .>= 0 .=> p n c) [induct2 p]

-- | Prove that sum of numbers from @0@ to @n@ is @n*(n-1)/2@.
--
-- We have:
--
-- >>> runKD sumProof
-- Lemma: sum_correct                      Q.E.D.
-- [Proven] sum_correct
sumProof :: KD Proof
sumProof = do
   let sum :: SInteger -> SInteger
       sum = smtFunction "sum" $ \n -> ite (n .== 0) 0 (n + sum (n - 1))

       spec :: SInteger -> SInteger
       spec n = (n * (n+1)) `sDiv` 2

       p :: SInteger -> SBool
       p n = observe "imp" (sum n) .== observe "spec" (spec n)

   lemma "sum_correct" (\(Forall @"n" n) -> n .>= 0 .=> p n) [induct p]

-- | Prove that sum of square of numbers from @0@ to @n@ is @n*(n+1)*(2n+1)/6@.
--
-- We have:
--
-- >>> runKD sumSquareProof
-- Lemma: sumSquare_correct                Q.E.D.
-- [Proven] sumSquare_correct
sumSquareProof :: KD Proof
sumSquareProof = do
   let sumSquare :: SInteger -> SInteger
       sumSquare = smtFunction "sumSquare" $ \n -> ite (n .== 0) 0 (n * n + sumSquare (n - 1))

       spec :: SInteger -> SInteger
       spec n = (n * (n+1) * (2*n+1)) `sDiv` 6

       p :: SInteger -> SBool
       p n = observe "imp" (sumSquare n) .== observe "spec" (spec n)

   lemma "sumSquare_correct" (\(Forall @"n" n) -> n .>= 0 .=> p n) [induct p]
