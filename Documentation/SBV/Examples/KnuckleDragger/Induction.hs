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

import Prelude hiding (sum, length)

import Data.SBV
import Data.SBV.Tools.KnuckleDragger
import Data.SBV.Tools.KnuckleDragger.Induction

import qualified Data.SBV.List as SL

-- | Prove that sum of numbers from @0@ to @n@ is @n*(n-1)/2@.
--
-- We have:
--
-- >>> sumProof
-- Axiom: Nat.induction                           Admitted.
-- Lemma: sum_correct                             Q.E.D.
sumProof :: IO Proven
sumProof = do
   let sum :: SInteger -> SInteger
       sum = smtFunction "sum" $ \n -> ite (n .== 0) 0 (n + sum (n - 1))

       spec :: SInteger -> SInteger
       spec n = (n * (n+1)) `sDiv` 2

       p :: SInteger -> SBool
       p n = sum n .== spec n

   induct <- inductionPrinciple p

   lemma "sum_correct" (\(Forall n) -> n .>= 0 .=> p n) [induct]

-- | Prove that sum of square of numbers from @0@ to @n@ is @n*(n+1)*(2n+1)/6@.
--
-- We have:
--
-- >>> sumSquareProof
-- Axiom: Nat.induction                           Admitted.
-- Lemma: sumSquare_correct                       Q.E.D.
sumSquareProof :: IO Proven
sumSquareProof = do
   let sumSquare :: SInteger -> SInteger
       sumSquare = smtFunction "sumSquare" $ \n -> ite (n .== 0) 0 (n * n + sumSquare (n - 1))

       spec :: SInteger -> SInteger
       spec n = (n * (n+1) * (2*n+1)) `sDiv` 6

       p :: SInteger -> SBool
       p n = sumSquare n .== spec n

   induct <- inductionPrinciple p

   lemma "sumSquare_correct" (\(Forall n) -> n .>= 0 .=> p n) [induct]

-- | Prove that the length of a list is one more than the length of its tail.
--
-- We have:
--
-- >>> listLengthProof
-- Axiom: List(a).induction                       Admitted.
-- Lemma: length_correct                          Q.E.D.
listLengthProof :: IO Proven
listLengthProof = do
   let length :: SList Integer -> SInteger
       length = smtFunction "length" $ \xs -> ite (SL.null xs) 0 (1 + length (SL.tail xs))

       spec :: SList Integer -> SInteger
       spec = SL.length

       p :: SList Integer -> SBool
       p xs = length xs .== spec xs

   induct <- inductionPrinciple p

   lemma "length_correct" (\(Forall xs) -> p xs) [induct]
