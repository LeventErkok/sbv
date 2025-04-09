-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.CaseSplit
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Use KnuckleDragger to prove @2n^2 + n + 1@ is never divisible by @3@.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.CaseSplit where

import Prelude hiding (sum, length)

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

-- | Prove that @2n^2 + n + 1@ is not divisible by @3@.
--
-- We have:
--
-- >>> notDiv3
-- Lemma: case_n_mod_3_eq_0
--   Asms: 1                               Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: case_n_mod_3_eq_1
--   Asms: 1                               Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: case_n_mod_3_eq_2
--   Asms: 1                               Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
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
notDiv3 = runKD $ do

   let s n = 2 * n * n + n + 1
       p n = s n `sEMod` 3 ./= 0

   -- Do the proof in 3 phases; one each for the possible value of n `mod` 3 being 0, 1, and 2
   -- Note that we use the euclidian definition of division/modulus.

   let case0 n = n `sEMod` 3 .== 0
       case1 n = n `sEMod` 3 .== 1
       case2 n = n `sEMod` 3 .== 2

   -- Case 0: n = 0 (mod 3)
   c0 <- calc "case_n_mod_3_eq_0"
              (\(Forall @"n" n) -> case0 n .=> p n) $
              \n -> [case0 n] |- s n                                       ?? case0 n
                              =: let w = some "witness" $ \k -> n .== 3*k  -- Grab the witness for the case
                              in s (3*w)
                              =: s (3*w)
                              =: 2*(3*w)*(3*w) + 3*w + 1
                              =: 18*w*w + 3*w + 1
                              =: 3*(6*w*w + w) + 1
                              =: qed

   -- Case 1: n = 1 (mod 3)
   c1 <- calc "case_n_mod_3_eq_1"
              (\(Forall @"n" n) -> case1 n .=> p n) $
              \n -> [case1 n] |- s n                                         ?? case1 n
                              =: let w = some "witness" $ \k -> n .== 3*k+1  -- Grab the witness for n being 1 modulo 3
                              in s (3*w+1)
                              =: 2*(3*w+1)*(3*w+1) + (3*w+1) + 1
                              =: 2*(9*w*w + 3*w + 3*w + 1) + (3*w + 1) + 1
                              =: 18*w*w + 12*w + 2 + 3*w + 2
                              =: 18*w*w + 15*w + 4
                              =: 3*(6*w*w + 5*w + 1) + 1
                              =: qed

   -- Case 2: n = 2 (mod 3)
   c2 <- calc "case_n_mod_3_eq_2"
              (\(Forall @"n" n) -> case2 n .=> p n) $
              \n -> [case2 n] |- s n                                        ?? case2 n
                              =: let w = some "witness" $ \k -> n .== 3*k+2 -- Grab the witness for n being 2 modulo 3
                              in s (3*w+2)
                              =: 2*(3*w+2)*(3*w+2) + (3*w+2) + 1
                              =: 2*(9*w*w + 6*w + 6*w + 4) + (3*w + 2) + 1
                              =: 18*w*w + 24*w + 8 + 3*w + 3
                              =: 18*w*w + 27*w + 11
                              =: 3*(6*w*w + 9*w + 3) + 2
                              =: qed

   calc "notDiv3"
        (\(Forall @"n" n) -> p n) $
        \n -> [] |- cases [ case0 n ==> p n ?? c0 `at` Inst @"n" n =: sTrue =: qed
                          , case1 n ==> p n ?? c1 `at` Inst @"n" n =: sTrue =: qed
                          , case2 n ==> p n ?? c2 `at` Inst @"n" n =: sTrue =: qed
                          ]
