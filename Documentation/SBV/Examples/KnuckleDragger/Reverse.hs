-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.Reverse
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Can we define the reverse function using no auxiliary functions, i.e., only
-- in terms of cons, head, tail, and itself (recursively)? This example
-- shows such a definition and proves that it is correct.
--
-- See Zohar Manna's 1974 "Mathematical Theory of Computation" book, where this
-- definition and its proof is presented as Example 5.36.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.Reverse where

import Prelude hiding (head, tail, null, reverse, length, init, last, (++))

import Data.SBV
import Data.SBV.List hiding (partition)
import Data.SBV.Tools.KnuckleDragger

-- * Reversing with no auxiliaries

-- | This definition of reverse uses no helper functions, other than the usual
-- head, tail, cons, and uncons to reverse a given list. Note that efficiency
-- is not our concern here, we call 'rev' itself three times in the body.
rev :: SList Integer -> SList Integer
rev = smtFunction "rev" $ \xs -> ite (null xs .|| null (tail xs)) xs
                                     (let (x, as)     = uncons xs
                                          (hras, tas) = uncons (rev as)
                                      in hras .: rev (x .: rev tas))

-- * Correctness proof

-- | Correctness the function 'rev'. We have:
--
-- >>> correctness
-- Inductive lemma: revSameLength
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: revApp
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: revCons                          Q.E.D.
-- Inductive lemma: reverseReverse
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma (strong): revCorrect
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way full case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2 (2 way full case split)
--       Step: 1.2.1                       Q.E.D.
--       Step: 1.2.2.1                     Q.E.D.
--       Step: 1.2.2.2                     Q.E.D.
--       Step: 1.2.2.3                     Q.E.D.
--       Step: 1.2.2.4                     Q.E.D.
--       Step: 1.2.2.5 (simplify head)     Q.E.D.
--       Step: 1.2.2.6                     Q.E.D.
--       Step: 1.2.2.7 (simplify tail)     Q.E.D.
--       Step: 1.2.2.8                     Q.E.D.
--       Step: 1.2.2.9                     Q.E.D.
--       Step: 1.2.2.10                    Q.E.D.
--       Step: 1.2.2.11 (substitute)       Q.E.D.
--       Step: 1.2.2.12                    Q.E.D.
--       Step: 1.2.2.13                    Q.E.D.
--       Step: 1.2.2.14                    Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] revCorrect
correctness :: IO Proof
correctness = runKD $ do

  -- Reverse: preserves length
  revSameLength <-
    induct "revSameLength"
           (\(Forall @"xs" (xs :: SList Integer)) -> length (reverse xs) .== length xs) $
           \ih (x :: SInteger) xs -> [] |- length (reverse (x .: xs))
                                        =: length (reverse xs ++ singleton x)
                                        =: length (reverse xs) + length (singleton x)
                                        ?? ih
                                        =: length xs + 1
                                        =: length (x .: xs)
                                        =: qed

  -- Reverse and append
  revApp  <-
     induct "revApp"
            (\(Forall @"xs" (xs :: SList Integer)) (Forall @"ys" ys) -> reverse (xs ++ ys) .== reverse ys ++ reverse xs) $
            \ih (x :: SInteger) xs ys ->
                [] |- reverse ((x .: xs) ++ ys)
                   =: reverse (x .: (xs ++ ys))
                   =: reverse (xs ++ ys) ++ singleton x
                   ?? ih
                   =: (reverse ys ++ reverse xs) ++ singleton x
                   =: reverse ys ++ (reverse xs ++ singleton x)
                   =: reverse ys ++ reverse (x .: xs)
                   =: qed

  -- A simpler version of revApp, for readability
  revCons <- lemma "revCons"
                   (\(Forall @"xs" (xs :: SList Integer)) (Forall @"x" x) -> reverse (xs ++ singleton x) .== x .:  reverse xs)
                   [revApp]

  -- Reverse: double reverse is identity
  revRev <-
    induct "reverseReverse"
           (\(Forall @"xs" (xs :: SList Integer)) -> reverse (reverse xs) .== xs) $
           \ih (x :: SInteger) xs -> [] |- reverse (reverse (x .: xs))
                                        =: reverse (reverse xs ++ singleton x)
                                        ?? revApp
                                        =: reverse (singleton x) ++ reverse (reverse xs)
                                        ?? ih
                                        =: singleton x ++ xs
                                        =: x .: xs
                                        =: qed

  sInductWith cvc5 "revCorrect"
    (\(Forall @"xs" xs) -> rev xs .== reverse xs)
    (length @Integer) $
    \ih xs -> []
           |- rev xs
           =: split xs trivial
                    (\a as -> split as trivial
                                    (\_ _ -> head (rev as) .: rev (a .: rev (tail (rev as)))
                                          ?? ih `at` Inst @"xs" as
                                          =: head (reverse as) .: rev (a .: rev (tail (reverse as)))
                                          ?? ih `at` Inst @"xs" (tail (rev as))
                                          =: head (reverse as) .: rev (a .: rev (tail (reverse as)))
                                          ?? revCons `at` (Inst @"xs" (init as), Inst @"x" (last as))
                                          =: let w = init as
                                                 b = last as
                                          in head (b .: reverse w) .: rev (a .: rev (tail (reverse as)))
                                          ?? "simplify head"
                                          =: b .: rev (a .: rev (tail (reverse as)))
                                          ?? revCons `at` (Inst @"xs" (init as), Inst @"x" (last as))
                                          =: b .: rev (a .: rev (tail (b .: reverse w)))
                                          ?? "simplify tail"
                                          =: b .: rev (a .: rev (reverse w))
                                          ?? [ ih `at` Inst @"xs" (reverse w)
                                             , revSameLength `at` Inst @"xs" w
                                             ]
                                          =: b .: rev (a .: reverse (reverse w))
                                          ?? revRev `at` Inst @"xs" w
                                          =: b .: rev (a .: w)
                                          ?? ih
                                          =: b .: reverse (a .: w)
                                          ?? "substitute"
                                          =: last as .: reverse (a .: init as)
                                          ?? revApp `at` (Inst @"xs" (init as), Inst @"ys" (singleton (last as)))
                                          =: reverse (a .: init as ++ singleton (last as))
                                          =: reverse (a .: as)
                                          =: reverse xs
                                          =: qed))
