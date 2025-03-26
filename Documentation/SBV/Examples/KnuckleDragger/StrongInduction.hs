-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.StrongInduction
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Examples of strong induction on integers.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP              #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.StrongInduction where

import Prelude hiding (length, null, tail)

import Data.SBV
import Data.SBV.List
import Data.SBV.Tools.KnuckleDragger

#ifndef HADDOCK
-- $setup
-- >>> -- For doctest purposes only:
-- >>> :set -XScopedTypeVariables
-- >>> import Control.Exception
#endif

-- | Prove that the sequence @1@, @3@, @S_{k-2} + 2 S_{k-1}@ is always odd.
--
-- We have:
--
-- >>> oddSequence1
-- Inductive lemma (strong): oddSequence
--   Step: 1 (3 way case split)
--       Asms: 1.1.1                       Q.E.D.
--       Step: 1.1.1                       Q.E.D.
--       Step: 1.1.2                       Q.E.D.
--       Asms: 1.2.1                       Q.E.D.
--       Step: 1.2.1                       Q.E.D.
--       Step: 1.2.2                       Q.E.D.
--       Asms: 1.3.1                       Q.E.D.
--       Step: 1.3.1                       Q.E.D.
--       Step: 1.3.2                       Q.E.D.
--       Step: 1.3.3                       Q.E.D.
--       Step: 1.3.4                       Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] oddSequence
oddSequence1 :: IO Proof
oddSequence1 = runKD $ do
  let s :: SInteger -> SInteger
      s = smtFunction "seq" $ \n -> ite (n .<= 0) 1
                                  $ ite (n .== 1) 3
                                  $ s (n-2) + 2 * s (n-1)

  -- z3 can't handle this, but CVC5 is proves it just fine.
  -- Note also that we do a "proof-by-contradiction," by deriving that
  -- the negation of the goal leads to falsehood.
  sInductWith cvc5 "oddSequence"
          (\(Forall @"n" n) -> n .>= 0 .=> sNot (2 `sDivides` s n)) $
          \ih n -> [n .>= 0] |- 2 `sDivides` s n
                             ?? n .>= 0
                             =: cases [ n .== 0 ==> sFalse =: qed
                                      , n .== 1 ==> sFalse =: qed
                                      , n .>= 2 ==>    2 `sDivides` (s (n-2) + 2 * s (n-1))
                                                    =: 2 `sDivides` s (n-2)
                                                    ?? ih `at` Inst @"n" (n - 2)
                                                    =: sFalse
                                                    =: qed
                                      ]

-- | Prove that the sequence @1@, @3@, @2 S_{k-1} - S_{k-2}@ generates sequence of odd numbers.
--
-- We have:
--
-- >>> oddSequence2
-- Lemma: oddSequence_0                    Q.E.D.
-- Lemma: oddSequence_1                    Q.E.D.
-- Inductive lemma (strong): oddSequence_sNp2
--   Asms: 1                               Q.E.D.
--   Step: 1                               Q.E.D.
--   Asms: 2                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Asms: 4                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: oddSequence2
--   Step: 1 (3 way case split)
--       Asms: 1.1.1                       Q.E.D.
--       Step: 1.1.1                       Q.E.D.
--       Step: 1.1.2                       Q.E.D.
--       Asms: 1.2.1                       Q.E.D.
--       Step: 1.2.1                       Q.E.D.
--       Step: 1.2.2                       Q.E.D.
--       Asms: 1.3.1                       Q.E.D.
--       Step: 1.3.1                       Q.E.D.
--       Asms: 1.3.2                       Q.E.D.
--       Step: 1.3.2                       Q.E.D.
--       Step: 1.3.3                       Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] oddSequence2
oddSequence2 :: IO Proof
oddSequence2 = runKD $ do
  let s :: SInteger -> SInteger
      s = smtFunction "seq" $ \n -> ite (n .<= 0) 1
                                  $ ite (n .== 1) 3
                                  $ 2 * s (n-1) - s (n-2)

  s0 <- lemma "oddSequence_0" (s 0 .== 1) []
  s1 <- lemma "oddSequence_1" (s 1 .== 3) []

  sNp2 <- sInduct "oddSequence_sNp2"
                  (\(Forall @"n" n) -> n .>= 2 .=> s n .== 2 * n + 1) $
                  \ih n -> [n .>= 2] |- s n
                                     ?? n .>= 2
                                     =: 2 * s (n-1) - s (n-2)
                                     ?? [ hyp (n .>= 2)
                                        , hprf (ih `at` Inst @"n" (n-1))
                                        ]
                                     =: 2 * (2 * (n-1) + 1) - s (n-2)
                                     ?? "simplify"
                                     =: 4*n - 4 + 2 - s (n-2)
                                     ?? [hyp (n .>= 2), hprf (ih `at` Inst @"n" (n-2))]
                                     =: 4*n - 2 - (2 * (n-2) + 1)
                                     ?? "simplify"
                                     =: 4*n - 2 - 2*n + 4 - 1
                                     =: 2*n + 1
                                     =: qed

  calc "oddSequence2" (\(Forall @"n" n) -> n .>= 0 .=> s n .== 2 * n + 1) $
                      \n -> [n .>= 0] |- s n
                                      ?? n .>= 0
                                      =: cases [ n .== 0 ==> (1 :: SInteger) =: qed
                                               , n .== 1 ==> (3 :: SInteger) =: qed
                                               , n .>= 2 ==>    s n
                                                             ?? [ hyp (n .>= 0)
                                                                , hprf s0
                                                                , hprf s1
                                                                , hprf $ sNp2 `at` Inst @"n" n
                                                                ]
                                                             =: 2 * n + 1
                                                             =: qed
                                               ]

-- | For strong induction to work, We have to instantiate the proof at a "smaller" value. This
-- example demonstrates what happens if we don't. We have:
--
-- >>> won'tProve1 `catch` (\(_ :: SomeException) -> pure ())
-- Inductive lemma (strong): lengthGood
--   Step: 1
-- *** Failed to prove lengthGood.1.
-- <BLANKLINE>
-- *** Solver reported: canceled
won'tProve1 :: IO ()
won'tProve1 = runKD $ do
   let len :: SList Integer -> SInteger
       len = smtFunction "len" $ \xs -> ite (null xs) 0 (1 + len (tail xs))

   -- Run it for 5 seconds, as otherwise z3 will hang as it can't prove make the inductive step
   _ <- sInductWith z3{extraArgs = ["-t:5000"]} "lengthGood"
                (\(Forall @"xs" xs) -> len xs .== length xs) $
                \ih xs -> [] |- len xs
                             -- incorrectly instantiate the IH at xs!
                             ?? ih `at` Inst @"xs" xs
                             =: length xs
                             =: qed
   pure ()

-- | Note that strong induction does not need an explicit base case, as the base-cases is folded into the
-- inductive step. Here's an example demonstrating what happens when the failure is only at the base case.
--
-- >>> won'tProve2 `catch` (\(_ :: SomeException) -> pure ())
-- Inductive lemma (strong): badLength
--   Step: 1
-- *** Failed to prove badLength.1.
-- Falsifiable. Counter-example:
--   xs = [] :: [Integer]
won'tProve2 :: IO ()
won'tProve2 = runKD $ do
   let len :: SList Integer -> SInteger
       len = smtFunction "badLength" $ \xs -> ite (null xs)
                                                  123
                                                  (ite (null xs)
                                                       0
                                                       (1 + len (tail xs)))

   _ <- sInduct "badLength"
                (\(Forall @"xs" xs) -> len xs .== length xs) $
                \ih xs -> [] |- len xs
                             ?? ih `at` Inst @"xs" xs
                             =: length xs
                             =: qed
   pure ()
