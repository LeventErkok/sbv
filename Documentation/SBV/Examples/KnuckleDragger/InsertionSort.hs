-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.InsertionSort
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving insertion sort correct.
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

-- * Insertion sort

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


-- * Helper functions

-- | A predicate testing whether a given list is non-decreasing.
nonDecreasing :: SList Integer -> SBool
nonDecreasing = smtFunction "nonDecreasing" $ \l ->  null l .|| null (tail l)
                                                 .|| let (x, l') = uncons l
                                                         (y, _)  = uncons l'
                                                     in x .<= y .&& nonDecreasing l'

-- | Remove the first occurrence of an number from a list, if any.
removeFirst :: SInteger -> SList Integer -> SList Integer
removeFirst = smtFunction "removeFirst" $ \e l -> ite (null l)
                                                      nil
                                                      (let (x, xs) = uncons l
                                                       in ite (e .== x) xs (x .: removeFirst e xs))

-- | Are two lists permutations of each other?
isPermutation :: SList Integer -> SList Integer -> SBool
isPermutation = smtFunction "isPermutation" $ \l r -> ite (null l)
                                                          (null r)
                                                          (let (x, xs) = uncons l
                                                           in x `elem` r .&& isPermutation xs (removeFirst x r))

-- * Correctness proof

-- | Correctness of insertion-sort. z3 struggles with this, but CVC5 proves it just fine.
--
-- We have:
--
-- >>> correctness
-- Lemma: nonDecTail                            Q.E.D.
-- Inductive lemma: insertNonDecreasing
--   Step: Base                                 Q.E.D.
--   Step: 1 (unfold insert)                    Q.E.D.
--   Step: 2 (push nonDecreasing down)          Q.E.D.
--   Step: 3 (unfold simplify)                  Q.E.D.
--   Step: 4                                    Q.E.D.
--   Step: 5                                    Q.E.D.
--   Result:                                    Q.E.D.
-- Inductive lemma: sortNonDecreasing
--   Step: Base                                 Q.E.D.
--   Step: 1 (unfold insertionSort)             Q.E.D.
--   Step: 2                                    Q.E.D.
--   Result:                                    Q.E.D.
-- Lemma: elemITE                               Q.E.D.
-- Inductive lemma: insertIsElem
--   Step: Base                                 Q.E.D.
--   Step: 1                                    Q.E.D.
--   Step: 2                                    Q.E.D.
--   Step: 3                                    Q.E.D.
--   Step: 4                                    Q.E.D.
--   Result:                                    Q.E.D.
-- Inductive lemma: removeAfterInsert
--   Step: Base                                 Q.E.D.
--   Step: 1 (expand insert)                    Q.E.D.
--   Step: 2 (push removeFirst down ite)        Q.E.D.
--   Step: 3 (unfold removeFirst on 'then')     Q.E.D.
--   Step: 4 (unfold removeFirst on 'else')     Q.E.D.
--   Step: 5                                    Q.E.D.
--   Step: 6 (simplify)                         Q.E.D.
--   Result:                                    Q.E.D.
-- Inductive lemma: sortIsPermutation
--   Step: Base                                 Q.E.D.
--   Step: 1                                    Q.E.D.
--   Step: 2                                    Q.E.D.
--   Step: 3                                    Q.E.D.
--   Step: 4                                    Q.E.D.
--   Step: 5                                    Q.E.D.
--   Result:                                    Q.E.D.
-- Lemma: insertionSortIsCorrect                Q.E.D.
-- [Proven] insertionSortIsCorrect
correctness :: IO Proof
correctness = runKDWith cvc5{kdOptions = (kdOptions cvc5) { ribbonLength = 45 }} $ do

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
                          ?? "unfold insert"
                          =: nonDecreasing (ite (e .<= x) (e .: x .: xs) (x .: insert e xs))
                          ?? "push nonDecreasing down"
                          =: ite (e .<= x) (nonDecreasing (e .: x .: xs))
                                           (nonDecreasing (x .: insert e xs))
                          ?? "unfold simplify"
                          =: ite (e .<= x)
                                 (nonDecreasing (x .: xs))
                                 (nonDecreasing (x .: insert e xs))
                          ?? nonDecreasing (x .: xs)
                          =: (e .> x .=> nonDecreasing (x .: insert e xs))
                          ?? [ nonDecrTail `at` (Inst @"x" x, Inst @"xs" (insert e xs))
                             , ih
                             ]
                          =: sTrue
                          =: qed

    sortNonDecreasing <-
        induct "sortNonDecreasing"
               (\(Forall @"xs" xs) -> nonDecreasing (insertionSort xs)) $
               \ih x xs -> [] |- nonDecreasing (insertionSort (x .: xs))
                              ?? "unfold insertionSort"
                              =: nonDecreasing (insert x (insertionSort xs))
                              ?? [ insertNonDecreasing `at` (Inst @"xs" (insertionSort xs), Inst @"e" x)
                                 , ih
                                 ]
                              =: sTrue
                              =: qed

    --------------------------------------------------------------------------------------------
    -- Part II. Prove that the output of insertion sort is a permuation of its input
    --------------------------------------------------------------------------------------------

    -- For whatever reason z3 can't figure this out in the below proof. This helper isn't needed for CVC5.
    -- Note that z3 is able to prove this out-of-the box without any helpers, but needs it in the next as a helper.
    elemITE <- lemma "elemITE" (\(Forall @"x" (x :: SInteger)) (Forall @"c" c) (Forall @"t" t) (Forall @"e" e)
                                        -> x `elem` ite c t e .== ite c (x `elem` t) (x `elem` e))
                     []

    insertIsElem <-
        induct "insertIsElem"
               (\(Forall @"xs" xs) (Forall @"e" e) -> e `elem` insert e xs) $
               \ih x xs e -> [] |- e `elem` insert e (x .: xs)
                                =: e `elem` ite (e .<= x) (e .: x .: xs) (x .: insert e xs)
                                -- z3 has hard time making the following step (though cvc5 is OK with it)
                                ?? elemITE `at` (Inst @"x" e, Inst @"c" (e .<= x), Inst @"t" (e .: x .: xs), Inst @"e" (x .: insert e xs))
                                =: ite (e .<= x) (e `elem` (e .: x .: xs)) (e `elem` (x .: insert e xs))
                                =: ite (e .<= x) sTrue (e `elem` insert e xs) ?? ih
                                =: sTrue
                                =: qed

    removeAfterInsert <-
        induct "removeAfterInsert"
               (\(Forall @"xs" xs) (Forall @"e" e) -> removeFirst e (insert e xs) .== xs) $
               \ih x xs e -> [] |- removeFirst e (insert e (x .: xs))
                                ??  "expand insert"
                                =: removeFirst e (ite (e .<= x) (e .: x .: xs) (x .: insert e xs))
                                ??  "push removeFirst down ite"
                                =: ite (e .<= x) (removeFirst e (e .: x .: xs)) (removeFirst e (x .: insert e xs))
                                ??  "unfold removeFirst on 'then'"
                                =: ite (e .<= x) (x .: xs) (removeFirst e (x .: insert e xs))
                                ??  "unfold removeFirst on 'else'"
                                =: ite (e .<= x) (x .: xs) (x .: removeFirst e (insert e xs))
                                ??  ih
                                =: ite (e .<= x) (x .: xs) (x .: xs)
                                ??  "simplify"
                                =: x .: xs
                                =: qed

    sortIsPermutation <-
        induct "sortIsPermutation"
               (\(Forall @"xs" xs) -> isPermutation xs (insertionSort xs)) $
               \ih x xs -> [] |- isPermutation (x .: xs) (insertionSort (x .: xs))
                              =: isPermutation (x .: xs) (insert x (insertionSort xs))
                              =: x `elem` insert x (insertionSort xs) .&& isPermutation xs (removeFirst x (insert x (insertionSort xs)))
                              ?? insertIsElem
                              =: isPermutation xs (removeFirst x (insert x (insertionSort xs)))
                              ?? removeAfterInsert
                              =: isPermutation xs (insertionSort xs)
                              ?? ih
                              =: sTrue
                              =: qed

    --------------------------------------------------------------------------------------------
    -- Put the two parts together for the final proof
    --------------------------------------------------------------------------------------------
    lemma "insertionSortIsCorrect"
          (\(Forall @"xs" xs) -> let out = insertionSort xs in nonDecreasing out .&& isPermutation xs out)
          [sortNonDecreasing, sortIsPermutation]
