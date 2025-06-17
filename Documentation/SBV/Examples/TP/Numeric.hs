-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Numeric
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Example use of inductive TP proofs, over integers.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Numeric where

import Prelude hiding (sum, length)

import Data.SBV
import Data.SBV.TP

#ifdef DOCTEST
-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> import Data.SBV.TP
-- >>> import Control.Exception
#endif

-- | Prove that sum of constants @c@ from @0@ to @n@ is @n*c@.
--
-- We have:
--
-- >>> runTP sumConstProof
-- Inductive lemma: sumConst_correct
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] sumConst_correct :: Ɐn ∷ Integer → Bool
sumConstProof :: TP (Proof (Forall "n" Integer -> SBool))
sumConstProof = do
   let c :: SInteger
       c = uninterpret "c"

       sum :: SInteger -> SInteger
       sum = smtFunction "sum" $ \n -> ite (n .== 0) 0 (c + sum (n - 1))

       spec :: SInteger -> SInteger
       spec n = c * n

   induct "sumConst_correct"
          (\(Forall n) -> n .>= 0 .=> sum n .== spec n) $
          \ih n -> [n .>= 0] |- sum (n+1)
                             =: c + sum n  ?? ih
                             =: c + spec n
                             =: c + c*n
                             =: c*(n+1)
                             =: spec (n+1)
                             =: qed

-- | Prove that sum of numbers from @0@ to @n@ is @n*(n-1)/2@.
--
-- >>> runTP sumProof
-- Inductive lemma: sum_correct
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] sum_correct :: Ɐn ∷ Integer → Bool
sumProof :: TP (Proof (Forall "n" Integer -> SBool))
sumProof = do
   let sum :: SInteger -> SInteger
       sum = smtFunction "sum" $ \n -> ite (n .<= 0) 0 (n + sum (n - 1))

       spec :: SInteger -> SInteger
       spec n = (n * (n+1)) `sEDiv` 2

   induct "sum_correct"
          (\(Forall n) -> n .>= 0 .=> sum n .== spec n) $
          \ih n -> [n .>= 0] |- sum (n+1)
                             =: n+1 + sum n  ?? ih
                             =: n+1 + spec n
                             =: spec (n+1)
                             =: qed

-- | Prove that sum of square of numbers from @0@ to @n@ is @n*(n+1)*(2n+1)/6@.
--
-- >>> runTP sumSquareProof
-- Inductive lemma: sumSquare_correct
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] sumSquare_correct :: Ɐn ∷ Integer → Bool
sumSquareProof :: TP (Proof (Forall "n" Integer -> SBool))
sumSquareProof = do
   let sumSquare :: SInteger -> SInteger
       sumSquare = smtFunction "sumSquare" $ \n -> ite (n .<= 0) 0 (n * n + sumSquare (n - 1))

       spec :: SInteger -> SInteger
       spec n = (n * (n+1) * (2*n+1)) `sEDiv` 6

   induct "sumSquare_correct"
          (\(Forall @"n" n) -> n .>= 0 .=> sumSquare n .== spec n) $
          \ih n -> [n .>= 0] |- sumSquare (n+1)
                             =: (n+1)*(n+1) + sumSquare n ?? ih
                             =: (n+1)*(n+1) + spec n
                             =: spec (n+1)
                             =: qed

-- | Prove that @11^n - 4^n@ is always divisible by 7.
--
-- NB. As of Feb 2025, z3 struggles with the inductive step in this proof, but cvc5 performs just fine.
--
-- We have:
--
-- >>> runTP elevenMinusFour
-- Lemma: powN                             Q.E.D.
-- Inductive lemma: elevenMinusFour
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Step: 7                               Q.E.D.
--   Step: 8                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] elevenMinusFour :: Ɐn ∷ Integer → Bool
elevenMinusFour :: TP (Proof (Forall "n" Integer -> SBool))
elevenMinusFour = do
   let pow :: SInteger -> SInteger -> SInteger
       pow = smtFunction "pow" $ \x y -> ite (y .== 0) 1 (x * pow x (y - 1))

       emf :: SInteger -> SBool
       emf n = 7 `sDivides` (11 `pow` n - 4 `pow` n)

   -- helper
   powN <- lemma "powN" (\(Forall @"x" x) (Forall @"n" n) -> n .>= 0 .=> x `pow` (n+1) .== x * x `pow` n) []

   inductWith cvc5 "elevenMinusFour"
          (\(Forall n) -> n .>= 0 .=> emf n) $
          \ih n -> [n .>= 0]
                |- emf (n+1)
                =: 7 `sDivides` (11 `pow` (n+1) - 4 `pow` (n+1))
                ?? powN `at` (Inst @"x" 11, Inst @"n" n)
                =: 7 `sDivides` (11 * 11 `pow` n - 4 `pow` (n+1))
                ?? powN `at` (Inst @"x" 4, Inst @"n" n)
                =: 7 `sDivides` (11 * 11 `pow` n - 4 * 4 `pow` n)
                =: 7 `sDivides` (7 * 11 `pow` n + 4 * 11 `pow` n - 4 * 4 `pow` n)
                =: 7 `sDivides` (7 * 11 `pow` n + 4 * (11 `pow` n - 4 `pow` n))
                ?? ih
                =: let x = some "x" (\v -> 7*v .== 11 `pow` n - 4 `pow` n)   -- Apply the IH and grab the witness for it
                in 7 `sDivides` (7 * 11 `pow` n + 4 * 7 * x)
                =: 7 `sDivides` (7 * (11 `pow` n + 4 * x))
                =: sTrue
                =: qed

-- | A negative example: The regular inductive proof on integers (i.e., proving at @0@, assuming at @n@ and proving at
-- @n+1@ will not allow you to conclude things when @n < 0@. The following example demonstrates this with the most
-- obvious example:
--
-- >>> badNonNegative `catch` (\(_ :: SomeException) -> pure ())
-- Inductive lemma: badNonNegative
--   Step: Base                            Q.E.D.
--   Step: 1
-- *** Failed to prove badNonNegative.1.
-- Falsifiable. Counter-example:
--   n = -2 :: Integer
badNonNegative :: IO ()
badNonNegative = runTP $ do
    _ <- induct "badNonNegative"
                (\(Forall @"n" (n :: SInteger)) -> n .>= 0) $
                \ih n -> [] |- n + 1 .>= 0
                            ?? ih
                            =: sTrue
                            =: qed
    pure ()
