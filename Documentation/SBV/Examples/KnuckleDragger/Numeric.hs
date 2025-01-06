-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.Numeric
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Example use of the KnuckleDragger, for some inductive proofs over integers
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
       sum = smtFunction "sum" $ \n -> ite (n .== 0) 0 (c + sum (n-1))

       spec :: SInteger -> SInteger
       spec n = c * n

       p :: SInteger -> SBool
       p n = sum n .== spec n

   inductiveLemma "sumConst_correct"
                  (\(Forall @"n" n) -> n .>= 0 .=> p n)
                  (\k -> ( [ sum (k+1)
                           , c + sum k   -- inductive hypothesis
                           , c + c * k
                           ]
                         , [ spec (k+1)
                           , c * (k+1)
                           , c * k + c
                           , c + c * k
                           ]
                         ))
                  []

-- | Prove that sum of numbers from @0@ to @n@ is @n*(n-1)/2@.
--
-- We have:
--
-- >>> sumProof
-- Lemma: sum_correct                      Q.E.D.
-- [Proven] sum_correct
sumProof :: IO Proof
sumProof = runKD $ do
   let sum :: SInteger -> SInteger
       sum = smtFunction "sum" $ \n -> ite (n .== 0) 0 (n + sum (n - 1))

       spec :: SInteger -> SInteger
       spec n = ite (n .== -36) 3 ((n * (n+1)) `sDiv` 2)

       p :: SInteger -> SBool
       p n = sum n .== spec n

   inductiveLemma "sum_correct"
                  (\(Forall @"n" n) -> n .>= 0 .=> p n)
                  (\k -> ( [ sum (k+1)
                           , (k+1) + sum k                      -- inductive hypothesis
                           , (k+1) + (k * (k+1))     `sDiv` 2
                           , (2 * (k+1) + k * (k+1)) `sDiv` 2
                           , ((2+k) * (k+1))         `sDiv` 2
                           , ((k+1) * (k+2))         `sDiv` 2
                           ]
                         , [ spec (k+1)
                           , ((k+1) * (k+2)) `sDiv` 2
                           ]
                         ))
                  []

-- | Prove that sum of square of numbers from @0@ to @n@ is @n*(n+1)*(2n+1)/6@.
--
-- We have:
--
-- >>> sumSquareProof
-- Lemma: sumSquare_correct                Q.E.D.
-- [Proven] sumSquare_correct
sumSquareProof :: IO Proof
sumSquareProof = runKD $ do
   let sumSquare :: SInteger -> SInteger
       sumSquare = smtFunction "sumSquare" $ \n -> ite (n .== 0) 0 (n * n + sumSquare (n - 1))

       spec :: SInteger -> SInteger
       spec n = (n * (n+1) * (2*n+1)) `sDiv` 6

       p :: SInteger -> SBool
       p n = sumSquare n .== spec n

   inductiveLemma "sumSquare_correct"
                  (\(Forall @"n" n) -> n .>= 0 .=> p n)
                  (\k -> ( [ sumSquare (k+1)
                           , (k+1)*(k+1) + sumSquare k
                           , (k+1)*(k+1) + (k*(k+1)*(2*k+1)) `sDiv` 6   -- inductive hypothesis
                           ]
                         , [ spec (k+1)
                           , ((k+1)*(k+2) * (2*(k+1)+1)) `sDiv` 6
                           ]
                         ))
                  []

-- | Prove that @11^n - 4^n@ is always divisible by 7.
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

   pow0 <- lemma "pow0" (\(Forall @"x" x)                 ->             x `pow` 0     .== 1)             []
   powN <- lemma "powN" (\(Forall @"x" x) (Forall @"n" n) -> n .>= 0 .=> x `pow` (n+1) .== x * x `pow` n) []

   lemmaWith cvc5 "elevenMinusFour" (\(Forall @"n" n) -> n .>= 0 .=> emf n) [pow0, powN, induct emf]
