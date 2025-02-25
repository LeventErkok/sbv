-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.InsertionSort
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving insertion-sort correct.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.InsertionSort where

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

import Prelude hiding (null, length, head, tail, elem)
import Data.SBV.List

-- | Insert an element into an already sorted list in the correct place.
insert :: SInteger -> SList Integer -> SList Integer
insert = smtFunction "insert" $ \e l -> ite (null l) (singleton e)
                                      $ let (x, xs) = uncons l
                                        in ite (e .<= x) (e .: x .: xs) (x .: insert e xs)

-- | Insertion sort, using 'insert' above to successively insert the elements.
insertionSort :: SList Integer -> SList Integer
insertionSort = smtFunction "insertionSort" $ \l -> ite (null l) nil
                                                  $ let (x, xs) = uncons l
                                                    in insert x (insertionSort xs)


-- | A predicate testing whether a given list is non-decreasing.
nonDecreasing :: SList Integer -> SBool
nonDecreasing = smtFunction "nonDecreasing" $ \l ->  null l .|| null (tail l)
                                                 .|| let (x, l') = uncons l
                                                         (y, _)  = uncons l'
                                                     in x .<= y .&& nonDecreasing l'

-- | Correctness of insertion-sort.
--
-- We have:
--
-- >>> correctness
-- Lemma: nonDecTail                       Q.E.D.
-- Inductive lemma: insertNonDecreasing
--   Base: insertNonDecreasing.Base        Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Asms: 4                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Asms: 5                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: insertNonDecreasing.Step        Q.E.D.
-- Lemma: insertionSort1                   Q.E.D.
-- Inductive lemma: sortNonDecreasing
--   Base: sortNonDecreasing.Base          Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: sortNonDecreasing.Step          Q.E.D.
-- Inductive lemma: insertIsElem
--   Base: insertIsElem.Base               Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: insertIsElem.Step               Q.E.D.
-- Inductive lemma: removeAfterInsert
--   Base: removeAfterInsert.Base          Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Step: removeAfterInsert.Step          Q.E.D.
-- Inductive lemma: sortIsPermutation
--   Base: sortIsPermutation.Base          Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: sortIsPermutation.Step          Q.E.D.
-- Lemma: insertionSortIsCorrect           Q.E.D.
correctness :: IO Proof
correctness = runKD $ do

    --------------------------------------------------------------------------------------------
    -- Part I. Prove that the output of insertion sort is non-decreasing.
    --------------------------------------------------------------------------------------------

    nonDecrTail <- lemma "nonDecTail"
                         (\(Forall @"x" x) (Forall @"xs" xs) -> nonDecreasing (x .: xs) .=> nonDecreasing xs)
                         []

    insertNonDecreasing <-
        induct "insertNonDecreasing"
               (\(Forall @"xs" xs) (Forall @"e" e) -> nonDecreasing xs .=> nonDecreasing (insert e xs)) $
               \ih x xs e -> [nonDecreasing (x .: xs)]
                          |- nonDecreasing (insert e (x .: xs))
                          ? "unfold insert"
                          =: nonDecreasing (ite (e .<= x) (e .: x .: xs) (x .: insert e xs))
                          ? "push nonDecreasing over the ite"
                          =: ite (e .<= x) (nonDecreasing (e .: x .: xs))
                                           (nonDecreasing (x .: insert e xs))
                          ? "unfold nonDecreasing, simplify"
                          =: ite (e .<= x)
                                 (nonDecreasing (x .: xs))
                                 (nonDecreasing (x .: insert e xs))
                          ?  nonDecreasing (x .: xs)
                          =: (e .> x .=> nonDecreasing (x .: insert e xs))
                          ? [ hyp  (nonDecreasing (x .: xs))
                            , hprf (nonDecrTail `at` (Inst @"x" x, Inst @"xs" (insert e xs)))
                            , hprf ih
                            ]
                          =: sTrue
                          =: qed


    -- Unfolding insertion sort just once. This helps z3, which otherwise gets stuck in the following proof.
    is1 <- lemma "insertionSort1" (\(Forall @"x" x) (Forall @"xs" xs) -> insertionSort (x .: xs) .== insert x (insertionSort xs)) []

    sortNonDecreasing <-
        induct "sortNonDecreasing"
               (\(Forall @"xs" xs) -> nonDecreasing (insertionSort xs)) $
               \ih x xs -> [] |- nonDecreasing (insertionSort (x .: xs))
                              -- Surprisingly, z3 really needs to be told how to instantiate is1 below so it doesn't get stuck.
                              ? is1 `at` (Inst @"x" x, Inst @"xs" xs)
                              =: nonDecreasing (insert x (insertionSort xs))
                              ? [ hprf (insertNonDecreasing `at` (Inst @"xs" (insertionSort xs), Inst @"e" x))
                                , hprf ih
                                ]
                              =: sTrue
                              =: qed

    --------------------------------------------------------------------------------------------
    -- Part II. Prove that the output of insertion sort is a permuation of its input
    --------------------------------------------------------------------------------------------
    let removeFirst :: SInteger -> SList Integer -> SList Integer
        removeFirst = smtFunction "removeFirst" $ \e l -> ite (null l)
                                                              nil
                                                              (let (x, xs) = uncons l
                                                               in ite (e .== x) xs (x .: removeFirst e xs))

        isPermutation :: SList Integer -> SList Integer -> SBool
        isPermutation = smtFunction "isPermutation" $ \l r -> ite (null l)
                                                                  (null r)
                                                                  (let (x, xs) = uncons l
                                                                   in x `elem` r .&& isPermutation xs (removeFirst x r))

    -- z3 is struggling with this goal, but cvc5 happily gets it
    insertIsElem <-
        inductWith cvc5 "insertIsElem"
               (\(Forall @"xs" xs) (Forall @"e" e) -> e `elem` insert e xs) $
               \ih x xs e -> [] |- e `elem` insert e (x .: xs)
                                =: e `elem` ite (e .<= x) (e .: x .: xs) (x .: insert e xs)
                                =: ite (e .<= x) (e `elem` (e .: x .: xs)) (e `elem` (x .: insert e xs))
                                =: ite (e .<= x) sTrue (e `elem` insert e xs) ? ih
                                =: sTrue
                                =: qed

    removeAfterInsert <-
        induct "removeAfterInsert"
               (\(Forall @"xs" xs) (Forall @"e" e) -> removeFirst e (insert e xs) .== xs) $
               \ih x xs e -> [] |- removeFirst e (insert e (x .: xs))
                                ?  "expand insert"
                                =: removeFirst e (ite (e .<= x) (e .: x .: xs) (x .: insert e xs))
                                ?  "push removeFirst down the if-then-else"
                                =: ite (e .<= x) (removeFirst e (e .: x .: xs)) (removeFirst e (x .: insert e xs))
                                ?  "unfold removeFirst, then branch"
                                =: ite (e .<= x) (x .: xs) (removeFirst e (x .: insert e xs))
                                ?  "unfold removeFirst,  else branch. Note that e .== x is False, due to the pre-condition"
                                =: ite (e .<= x) (x .: xs) (x .: removeFirst e (insert e xs))
                                ?  ih
                                =: ite (e .<= x) (x .: xs) (x .: xs)
                                ?  "simplify"
                                =: x .: xs
                                =: qed

    sortIsPermutation <-
        induct "sortIsPermutation"
               (\(Forall @"xs" xs) -> isPermutation xs (insertionSort xs)) $
               \ih x xs -> [] |- isPermutation (x .: xs) (insertionSort (x .: xs))
                              =: isPermutation (x .: xs) (insert x (insertionSort xs))
                              =: x `elem` insert x (insertionSort xs) .&& isPermutation xs (removeFirst x (insert x (insertionSort xs)))
                              ? insertIsElem
                              =: isPermutation xs (removeFirst x (insert x (insertionSort xs)))
                              ? removeAfterInsert
                              =: isPermutation xs (insertionSort xs)
                              ? ih
                              =: sTrue
                              =: qed

    --------------------------------------------------------------------------------------------
    -- Put the two parts together for the final proof
    --------------------------------------------------------------------------------------------
    lemma "insertionSortIsCorrect"
          (\(Forall @"xs" xs) -> let out = insertionSort xs in nonDecreasing out .&& isPermutation xs out)
          [sortNonDecreasing, sortIsPermutation]
