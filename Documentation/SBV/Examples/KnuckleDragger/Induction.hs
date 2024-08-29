-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.Induction
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Example use of the KnuckleDragger, for some inductive proofs
--
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.Induction where

import Prelude hiding (sum)

import Data.SBV
import Data.SBV.Tools.KnuckleDragger
import Data.SBV.Tools.KnuckleDragger.Induction

-- | Prove that sum of numbers from @0@ to @n@ is @n*(n-1)/2@.
--
-- We have:
--
-- >>> sumProof
-- Axiom: sum_induction                           Admitted.
-- Lemma: sum_correct                             Q.E.D.
sumProof :: IO Proven
sumProof = do
   let sum :: SInteger -> SInteger
       sum = smtFunction "sum" $ \n -> ite (n .== 0) 0 (n + sum (n - 1))

       spec :: SInteger -> SInteger
       spec n = (n * (n+1)) `sDiv` 2

   (p, induct) <- inductionPrinciple "sum" (\n -> sum n .== spec n)

   lemma "sum_correct" (\(Forall n) -> p n) [induct]

-- | Prove that sum of square of numbers from @0@ to @n@ is @n*(n+1)*(2n+1)/6@.
--
-- We have:
--
-- >>> sumSquareProof
-- Axiom: sumSquare_induction                     Admitted.
-- Lemma: sumSquare_correct                       Q.E.D.
sumSquareProof :: IO Proven
sumSquareProof = do
   let sumSquare :: SInteger -> SInteger
       sumSquare = smtFunction "sumSquare" $ \n -> ite (n .== 0) 0 (n * n + sumSquare (n - 1))

       spec :: SInteger -> SInteger
       spec n = (n * (n+1) * (2*n+1)) `sDiv` 6

   (p, induct) <- inductionPrinciple "sumSquare" (\n -> sumSquare n .== spec n)

   lemma "sumSquare_correct" (\(Forall n) -> p n) [induct]
