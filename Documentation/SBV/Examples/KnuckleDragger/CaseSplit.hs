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

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.CaseSplit where

import Prelude hiding (sum, length)

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

-- | The default settings for z3 have trouble running this proof out-of-the-box.
-- We have to pass auto_config=false to z3!
z3NoAutoConfig :: SMTConfig
z3NoAutoConfig = z3{extraArgs = ["auto_config=false"]}

-- | Prove that @2n^2 + n + 1@ is not divisible by @3@.
--
-- We have:
--
-- >>> notDiv3
-- Chain lemma: case_n_mod_3_eq_0
--   Step  : 1                             Q.E.D.
--   Step  : 2                             Q.E.D.
--   Result:                               Q.E.D.
-- Chain lemma: case_n_mod_3_eq_1
--   Step  : 1                             Q.E.D.
--   Step  : 2                             Q.E.D.
--   Result:                               Q.E.D.
-- Chain lemma: case_n_mod_3_eq_2
--   Step  : 1                             Q.E.D.
--   Step  : 2                             Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: notDiv3                          Q.E.D.
-- [Proven] notDiv3
notDiv3 :: IO Proof
notDiv3 = runKDWith z3NoAutoConfig $ do

   let s n = 2 * n * n + n + 1
       p n = s n `sEMod` 3 ./= 0

   -- Do the proof in 3 phases; one each for the possible value of n `mod` 3 being 0, 1, and 2
   -- Note that we use the euclidian definition of division/modulus.

   -- Case 0: n = 0 (mod 3)
   case0 <- chainLemma "case_n_mod_3_eq_0"
                       (\(Forall @"n" n) -> (n `sEMod` 3 .== 0) .=> p n)
                       (pure ())
                       (\n -> let k = n `sEDiv` 3
                              in [ n `sEMod` 3 .== 0
                                 , n .== 3 * k
                                 , s n .== s (3 * k)
                                 ])
                       []

   -- Case 1: n = 1 (mod 3)
   case1 <- chainLemma "case_n_mod_3_eq_1"
                       (\(Forall @"n" n) -> (n `sEMod` 3 .== 1) .=> p n)
                       (pure ())
                       (\n -> let k = n `sEDiv` 3
                              in [ n `sEMod` 3 .== 1
                                 , n .== 3 * k + 1
                                 , s n .== s (3 * k + 1)
                                 ])
                       []

   -- Case 2: n = 2 (mod 3)
   case2 <- chainLemma "case_n_mod_3_eq_2"
                       (\(Forall @"n" n) -> (n `sEMod` 3 .== 2) .=> p n)
                       (pure ())
                       (\n -> let k = n `sEDiv` 3
                              in [ n `sEMod` 3 .== 2
                                 , n .== 3 * k + 2
                                 , s n .== s (3 * k + 2)
                                 ])
                       []

   -- Note that z3 is smart enough to figure out the above cases are complete, so
   -- no extra completeness helper is needed.
   lemma "notDiv3"
         (\(Forall @"n" n) -> p n)
         [case0, case1, case2]
