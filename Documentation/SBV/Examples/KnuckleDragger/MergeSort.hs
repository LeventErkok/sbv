-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.MergeSort
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving merge-sort correct.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.MergeSort where

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

import Prelude hiding (null, length, head, tail, elem, splitAt)
import Data.SBV.List

-- * Merge sort

-- | Merge two already sorted lists into another
merge :: SList Integer -> SList Integer -> SList Integer
merge = smtFunction "merge" $ \l r -> ite (null l) r
                                    $ ite (null r) l
                                    $ let (a, as) = uncons l
                                          (b, bs) = uncons r
                                      in ite (a .<= b) (a .: merge as r) (b .: merge l bs)

-- | Merge sort, using 'merge' above to successively sort halved input
mergeSort :: SList Integer -> SList Integer
mergeSort = smtFunction "mergeSort" $ \l -> ite (length l .<= 1) l
                                              $ let (h1, h2) = splitAt (length l `sEDiv` 2) l
                                                in merge (mergeSort h1) (mergeSort h2)
-- * Helper functions

-- | A predicate testing whether a given list is non-decreasing.
nonDecreasing :: SList Integer -> SBool
nonDecreasing = smtFunction "nonDecreasing" $ \l ->  null l .|| null (tail l)
                                                 .|| let (x, l') = uncons l
                                                         (y, _)  = uncons l'
                                                     in x .<= y .&& nonDecreasing l'

-- | Remove the first occurrance of an number from a list, if any.
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

-- | Correctness of merge-sort.
--
-- We have:
--
-- >>> correctness
correctness :: IO Proof
correctness = runKD $ do

    --------------------------------------------------------------------------------------------
    -- Part I. Prove that the output of merge sort is non-decreasing.
    --------------------------------------------------------------------------------------------

    mergeKeepsSort <-
        induct "mergeKeepsSort"
               (\(Forall @"xs" xs) (Forall @"ys" ys) -> nonDecreasing xs .&& nonDecreasing ys .=> nonDecreasing (merge xs ys)) $
               \_h x xs ys -> [nonDecreasing (x .: xs), nonDecreasing ys]
                           |- nonDecreasing (merge (x .: xs) ys)
                           ?  "case split on ys, simplify"
                           =: ite (null ys)
                                  (nonDecreasing (merge (x .: xs) nil))
                                  (sNot (null ys) .=> nonDecreasing (merge (x .: xs) (head ys .: tail ys)))
                           ?  nonDecreasing (x .: xs)
                           =: (null ys .|| nonDecreasing (merge (x .: xs) (head ys .: tail ys)))
                           ?  "case split: x .<= head ys"
                           =: (null ys .|| nonDecreasing (ite (x .<= head ys)
                                                              (x       .: merge xs ys)
                                                              (head ys .: merge (x .: xs) ys)))
                           ?  "push nonDecreasing through ite"
                           =: null ys .|| (ite (x .<= head ys)
                                               (nonDecreasing (x       .: merge xs ys))
                                               (nonDecreasing (head ys .: merge (x .: xs) ys)))
                           =: qed

    sortNonDecreasing <-
        lemma "sortNonDecreasing"
              (\(Forall @"xs" xs) -> nonDecreasing (mergeSort xs))
              [mergeKeepsSort]

    --------------------------------------------------------------------------------------------
    -- Part II. Prove that the output of merge sort is a permuation of its input
    --------------------------------------------------------------------------------------------

    sortIsPermutation <-
        lemma  "sortIsPermutation"
               (\(Forall @"xs" xs) -> isPermutation xs (mergeSort xs))
               [sorry]

    --------------------------------------------------------------------------------------------
    -- Put the two parts together for the final proof
    --------------------------------------------------------------------------------------------
    lemma "mergeSortIsCorrect"
          (\(Forall @"xs" xs) -> let out = mergeSort xs in nonDecreasing out .&& isPermutation xs out)
          [sortNonDecreasing, sortIsPermutation]
