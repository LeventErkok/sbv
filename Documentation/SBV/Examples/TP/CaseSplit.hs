-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.CaseSplit
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Use TP to prove @2n^2 + n + 1@ is never divisible by @3@.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.CaseSplit where

import Prelude hiding (sum, length)

import Data.SBV
import Data.SBV.Tools.TP

-- | Prove that @2n^2 + n + 1@ is not divisible by @3@.
--
-- We have:
--
-- >>> notDiv3
-- Lemma: case_n_mod_3_eq_0
--   Step: 1                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: case_n_mod_3_eq_1
--   Step: 1                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: case_n_mod_3_eq_2
--   Step: 1                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: notDiv3
--   Step: 1 (3 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2                           Q.E.D.
--     Step: 1.3                           Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] notDiv3
notDiv3 :: IO Proof
notDiv3 = runTP $ do

   let s n = 2 * n * n + n + 1
       p n = s n `sEMod` 3 ./= 0

   -- Do the proof in 3 phases; one each for the possible value of n `mod` 3 being 0, 1, and 2
   -- Note that we use the euclidian definition of division/modulus.
   let case0 n = n `sEMod` 3 .== 0
       case1 n = n `sEMod` 3 .== 1
       case2 n = n `sEMod` 3 .== 2

   -- In each case, we grab the witness that makes the case true, and z3 can handle
   -- the rest by itself.

   -- Case 0: n = 0 (mod 3)
   c0 <- calc "case_n_mod_3_eq_0"
              (\(Forall @"n" n) -> case0 n .=> p n) $
              \n -> [case0 n] |- s n =: s (0 + 3 * (some "k" $ \k -> n .== 3*k+0)) =: qed

   -- Case 1: n = 1 (mod 3)
   c1 <- calc "case_n_mod_3_eq_1"
              (\(Forall @"n" n) -> case1 n .=> p n) $
              \n -> [case1 n] |- s n =: s (1 + 3 * (some "k" $ \k -> n .== 3*k+1)) =: qed

   -- Case 2: n = 2 (mod 3)
   c2 <- calc "case_n_mod_3_eq_2"
              (\(Forall @"n" n) -> case2 n .=> p n) $
              \n -> [case2 n] |- s n =: s (2 + 3 * (some "k" $ \k -> n .== 3*k+2)) =: qed

   calc "notDiv3"
        (\(Forall @"n" n) -> p n) $
        \n -> [] |- cases [ case0 n ==> p n ?? c0 `at` Inst @"n" n =: sTrue =: qed
                          , case1 n ==> p n ?? c1 `at` Inst @"n" n =: sTrue =: qed
                          , case2 n ==> p n ?? c2 `at` Inst @"n" n =: sTrue =: qed
                          ]
