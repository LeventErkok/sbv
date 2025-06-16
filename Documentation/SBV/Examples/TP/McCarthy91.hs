-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.McCarthy91
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving McCarthy's 91 function correct.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.McCarthy91 where

import Data.SBV
import Data.SBV.TP

-- * Definitions

-- | Nested recursive definition of McCarthy's function.
mcCarthy91 :: SInteger -> SInteger
mcCarthy91 = smtFunction "mcCarthy91" $ \n -> ite (n .> 100)
                                                  (n - 10)
                                                  (mcCarthy91 (mcCarthy91 (n + 11)))
-- | Specification for McCarthy's function.
spec91 :: SInteger -> SInteger
spec91 n = ite (n .> 100) (n - 10) 91

-- * Correctness

-- | We prove the equivalence of the nested recursive definition against the spec with a case analysis
-- and strong induction. We have:
--
-- >>> correctness
-- Lemma: case1                            Q.E.D.
-- Lemma: case2                            Q.E.D.
-- Inductive lemma (strong): case3
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (unfold)                      Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: mcCarthy91
--   Step: 1 (3 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2                           Q.E.D.
--     Step: 1.3                           Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] mcCarthy91
correctness :: IO (Proof (Forall "n" Integer -> SBool))
correctness = runTP $ do

   -- Case 1. When @n > 100@
   case1 <- lemma "case1" (\(Forall @"n" n) -> n .>= 100 .=> mcCarthy91 n .== spec91 n) []

   -- Case 2. When @90 <= n <= 100@
   case2 <- lemma "case2" (\(Forall @"n" n) -> 90 .<= n .&& n .<= 100 .=> mcCarthy91 n .== spec91 n) []

   -- Case 3. When @n < 90@. The crucial point here is the measure, which makes sure 101 < 100 < 99 < ...
   case3 <- sInduct "case3"
                    (\(Forall @"n" n) -> n .< 90 .=> mcCarthy91 n .== spec91 n)
                    (\n -> Measure (abs (101 - n))) $
                    \ih n -> [n .< 90] |- mcCarthy91 n
                                       ?? "unfold"
                                       =: mcCarthy91 (mcCarthy91 (n + 11))
                                       ?? ih `at` Inst @"n" (n + 11)
                                       =: mcCarthy91 91
                                       =: qed

   -- Putting it all together
   calc "mcCarthy91"
        (\(Forall n) -> mcCarthy91 n .== spec91 n) $
        \n -> [] |- cases [ n .> 100               ==> mcCarthy91 n ?? case1 =: spec91 n =: qed
                          , 90 .<= n .&& n .<= 100 ==> mcCarthy91 n ?? case2 =: spec91 n =: qed
                          , n .< 90                ==> mcCarthy91 n ?? case3 =: spec91 n =: qed
                          ]
