-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.StrongInduction
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Examples of strong induction.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.StrongInduction where

import Prelude hiding (length, null, head, tail, reverse, (++), splitAt, sum)

import Data.SBV
import Data.SBV.List
import Data.SBV.TP

#ifdef DOCTEST
-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> import Control.Exception
#endif

-- * Numeric examples

-- | Prove that the sequence @1@, @3@, @S_{k-2} + 2 S_{k-1}@ is always odd.
--
-- We have:
--
-- >>> oddSequence1
-- Inductive lemma (strong): oddSequence
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (3 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2                           Q.E.D.
--     Step: 1.3.1                         Q.E.D.
--     Step: 1.3.2                         Q.E.D.
--     Step: 1.3.3                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] oddSequence
oddSequence1 :: IO Proof
oddSequence1 = runTP $ do
  let s :: SInteger -> SInteger
      s = smtFunction "seq" $ \n -> ite (n .<= 0) 1
                                  $ ite (n .== 1) 3
                                  $ s (n-2) + 2 * s (n-1)

  -- z3 can't handle this, but CVC5 is proves it just fine.
  -- Note also that we do a "proof-by-contradiction," by deriving that
  -- the negation of the goal leads to falsehood.
  sInductWith cvc5 "oddSequence"
          (\(Forall @"n" n) -> n .>= 0 .=> sNot (2 `sDivides` s n)) (abs @SInteger) $
          \ih n -> [n .>= 0] |- 2 `sDivides` s n
                             =: cases [ n .== 0 ==> contradiction
                                      , n .== 1 ==> contradiction
                                      , n .>= 2 ==> 2 `sDivides` (s (n-2) + 2 * s (n-1))
                                                 =: 2 `sDivides` s (n-2)
                                                 ?? ih `at` Inst @"n" (n - 2)
                                                 =: contradiction
                                      ]

-- | Prove that the sequence @1@, @3@, @2 S_{k-1} - S_{k-2}@ generates sequence of odd numbers.
--
-- We have:
--
-- >>> oddSequence2
-- Lemma: oddSequence_0                              Q.E.D.
-- Lemma: oddSequence_1                              Q.E.D.
-- Inductive lemma (strong): oddSequence_sNp2
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1                                         Q.E.D.
--   Step: 2                                         Q.E.D.
--   Step: 3 (simplify)                              Q.E.D.
--   Step: 4                                         Q.E.D.
--   Step: 5 (simplify)                              Q.E.D.
--   Step: 6                                         Q.E.D.
--   Result:                                         Q.E.D.
-- Lemma: oddSequence2
--   Step: 1 (3 way case split)
--     Step: 1.1                                     Q.E.D.
--     Step: 1.2                                     Q.E.D.
--     Step: 1.3.1                                   Q.E.D.
--     Step: 1.3.2                                   Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- [Proven] oddSequence2
oddSequence2 :: IO Proof
oddSequence2 = runTPWith (tpRibbon 50 z3) $ do
  let s :: SInteger -> SInteger
      s = smtFunction "seq" $ \n -> ite (n .<= 0) 1
                                  $ ite (n .== 1) 3
                                  $ 2 * s (n-1) - s (n-2)

  s0 <- lemma "oddSequence_0" (s 0 .== 1) []
  s1 <- lemma "oddSequence_1" (s 1 .== 3) []

  sNp2 <- sInduct "oddSequence_sNp2"
                  (\(Forall @"n" n) -> n .>= 2 .=> s n .== 2 * n + 1) (abs @SInteger) $
                  \ih n -> [n .>= 2] |- s n
                                     =: 2 * s (n-1) - s (n-2)
                                     ?? ih `at` Inst @"n" (n-1)
                                     =: 2 * (2 * (n-1) + 1) - s (n-2)
                                     ?? "simplify"
                                     =: 4*n - 4 + 2 - s (n-2)
                                     ?? ih `at` Inst @"n" (n-2)
                                     =: 4*n - 2 - (2 * (n-2) + 1)
                                     ?? "simplify"
                                     =: 4*n - 2 - 2*n + 4 - 1
                                     =: 2*n + 1
                                     =: qed

  calc "oddSequence2" (\(Forall @"n" n) -> n .>= 0 .=> s n .== 2 * n + 1) $
                      \n -> [n .>= 0] |- s n
                                      =: cases [ n .== 0 ==> (1 :: SInteger) =: qed
                                               , n .== 1 ==> (3 :: SInteger) =: qed
                                               , n .>= 2 ==>    s n
                                                             ?? [ s0
                                                                , s1
                                                                , sNp2 `at` Inst @"n" n
                                                                ]
                                                             =: 2 * n + 1
                                                             =: qed
                                               ]

-- * Strong induction checks

-- | For strong induction to work, We have to instantiate the proof at a "smaller" value. This
-- example demonstrates what happens if we don't. We have:
--
-- >>> won'tProve1 `catch` (\(_ :: SomeException) -> pure ())
-- Inductive lemma (strong): lengthGood
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1
-- *** Failed to prove lengthGood.1.
-- <BLANKLINE>
-- *** Solver reported: canceled
won'tProve1 :: IO ()
won'tProve1 = runTP $ do
   let len :: SList Integer -> SInteger
       len = smtFunction "len" $ \xs -> ite (null xs) 0 (1 + len (tail xs))

   -- Run it for 5 seconds, as otherwise z3 will hang as it can't prove make the inductive step
   _ <- sInductWith z3{extraArgs = ["-t:5000"]} "lengthGood"
                (\(Forall @"xs" xs) -> len xs .== length xs)
                (length @Integer) $
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
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1
-- *** Failed to prove badLength.1.
-- Falsifiable. Counter-example:
--   xs = [] :: [Integer]
won'tProve2 :: IO ()
won'tProve2 = runTP $ do
   let len :: SList Integer -> SInteger
       len = smtFunction "badLength" $ \xs -> ite (null xs)
                                                  123
                                                  (ite (null xs)
                                                       0
                                                       (1 + len (tail xs)))

   _ <- sInduct "badLength"
                (\(Forall @"xs" xs) -> len xs .== length xs)
                (length @Integer) $
                \ih xs -> [] |- len xs
                             ?? ih `at` Inst @"xs" xs
                             =: length xs
                             =: qed
   pure ()

-- | The measure for strong induction should always produce a non-negative measure. The measure, in general, is an integer, or
-- a tuple of integers, for tuples upto size 5. The ordering is lexicographic. This allows us to do proofs over 5-different arguments
-- where their total measure goes down. If the measure can be negative, then we flag that as a failure, as demonstrated here. We have:
--
-- >>> won'tProve3 `catch` (\(_ :: SomeException) -> pure ())
-- Inductive lemma (strong): badMeasure
--   Step: Measure is non-negative
-- *** Failed to prove badMeasure.Measure is non-negative.
-- Falsifiable. Counter-example:
--   x = -1 :: Integer
won'tProve3 :: IO ()
won'tProve3 = runTP $ do
   _ <- sInduct "badMeasure"
                (\(Forall @"x" (x :: SInteger)) -> x .== x)
                (id @SInteger) $
                \_h (x :: SInteger) -> [] |- x
                                          =: x
                                          =: qed

   pure ()

-- | The measure must always go down using lexicographic ordering. If not, SBV will flag this as a failure. We have:
--
-- >>> won'tProve4 `catch` (\(_ :: SomeException) -> pure ())
-- Inductive lemma (strong): badMeasure
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2
-- *** Failed to prove badMeasure.1.2.2.
-- <BLANKLINE>
-- *** Solver reported: canceled
won'tProve4 :: IO ()
won'tProve4 = runTP $ do

   let -- a bizarre (but valid!) way to sum two integers
       weirdSum = smtFunction "weirdSum" (\x y -> ite (x .<= 0) y (weirdSum (x - 1) (y + 1)))

   _ <- sInductWith z3{extraArgs = ["-t:5000"]} "badMeasure"
                (\(Forall @"x" (x :: SInteger)) (Forall @"y" (y :: SInteger)) -> x .>= 0 .=> weirdSum x y .== x + y)
                -- This measure is not good, since it remains the same. Note that we do not get a
                -- failure, but the proof will never converge either; so we put a time bound
                (\x y -> abs x + abs @SInteger y) $
                \ih (x :: SInteger) (y :: SInteger) ->
                    [x .>= 0] |- ite (x .<= 0) y (weirdSum (x - 1) (y + 1))
                              =: cases [ x .<= 0 ==> trivial
                                       , x .>  0 ==> weirdSum (x - 1) (y + 1)
                                                  ?? ih `at` (Inst @"x" (x - 1), Inst @"y" (y + 1))
                                                  =: x - 1 + y + 1
                                                  =: x + y
                                                  =: qed
                                       ]

   pure ()

-- * Summing via halving

-- | We prove that summing a list can be done by halving the list, summing parts, and adding the results. The proof uses
-- strong induction. We have:
--
-- >>> sumHalves
-- Inductive lemma: sumAppend
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma (strong): sumHalves
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way full case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2 (2 way full case split)
--       Step: 1.2.1                       Q.E.D.
--       Step: 1.2.2.1                     Q.E.D.
--       Step: 1.2.2.2                     Q.E.D.
--       Step: 1.2.2.3                     Q.E.D.
--       Step: 1.2.2.4                     Q.E.D.
--       Step: 1.2.2.5                     Q.E.D.
--       Step: 1.2.2.6 (simplify)          Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] sumHalves
sumHalves :: IO Proof
sumHalves = runTP $ do

    let halvingSum :: SList Integer -> SInteger
        halvingSum = smtFunction "halvingSum" $ \xs -> ite (null xs .|| null (tail xs))
                                                           (sum xs)
                                                           (let (f, s) = splitAt (length xs `sDiv` 2) xs
                                                            in halvingSum f + halvingSum s)

    helper <- induct "sumAppend"
                     (\(Forall @"xs" xs) (Forall @"ys" ys) -> sum @Integer (xs ++ ys) .== sum xs + sum ys) $
                     \ih x xs ys -> [] |- sum @Integer (x .: xs ++ ys)
                                       =: x + sum (xs ++ ys)
                                       ?? ih
                                       =: x + sum xs + sum ys
                                       =: sum (x .: xs) + sum ys
                                       =: qed

    -- Use strong induction to prove the theorem. CVC5 solves this with ease, but z3 struggles.
    sInductWith cvc5 "sumHalves"
      (\(Forall @"xs" xs) -> halvingSum xs .== sum xs)
      (length @Integer) $
      \ih xs -> [] |- halvingSum xs
                   =: split xs qed
                            (\a as -> split as qed
                                            (\b bs -> halvingSum (a .: b .: bs)
                                                   =: let (f, s) = splitAt (length (a .: b .: bs) `sDiv` 2) (a .: b .: bs)
                                                   in halvingSum f + halvingSum s
                                                   ?? ih `at` Inst @"xs" f
                                                   =: sum f + halvingSum s
                                                   ?? ih `at` Inst @"xs" s
                                                   =: sum f + sum s
                                                   ?? helper `at` (Inst @"xs" f, Inst @"ys" s)
                                                   =: sum (f ++ s)
                                                   ?? "simplify"
                                                   =: sum (a .: b .: bs)
                                                   =: qed))
