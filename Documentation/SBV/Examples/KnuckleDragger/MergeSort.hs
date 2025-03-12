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
correctness = runKDWith z3{kdOptions = (kdOptions z3) {ribbonLength = 50}} $ do

    --------------------------------------------------------------------------------------------
    -- Part I. Prove that the output of merge sort is non-decreasing.
    --------------------------------------------------------------------------------------------

    nonDecrIns  <- lemma "nonDecrInsert"
                         (\(Forall @"x" x) (Forall @"ys" ys) -> nonDecreasing ys .&& sNot (null ys) .&& x .<= head ys
                                                            .=> nonDecreasing (x .: ys))
                         []

    nonDecrTail <- lemma "nonDecTail"
                         (\(Forall @"x" x) (Forall @"xs" xs) -> nonDecreasing (x .: xs) .=> nonDecreasing xs)
                         []

    mergeKeepsSort <-
        sInductWith cvc5 "mergeKeepsSort"
               (\(Forall @"xs" xs) (Forall @"ys" ys) -> nonDecreasing xs .&& nonDecreasing ys .=> nonDecreasing (merge xs ys)) $
               \ih x xs y ys -> [nonDecreasing (x .: xs), nonDecreasing (y .: ys)]
                             |- nonDecreasing (merge (x .: xs) (y .: ys))
                             ?? "unfold merge"
                             =: nonDecreasing (ite (x .<= y)
                                                   (x .: merge xs (y .: ys))
                                                   (y .: merge (x .: xs) ys))
                             ?? "push nonDecreasing down"
                             =: ite (x .<= y)
                                    (nonDecreasing (x .: merge xs (y .: ys)))
                                    (nonDecreasing (y .: merge (x .: xs) ys))
                             ?? [ hprf $ nonDecrIns `at` (Inst @"x" x, Inst @"ys" (merge xs (y .: ys)))
                                , hyp  $ nonDecreasing (x .: xs)
                                , hyp  $ nonDecreasing (y .: ys)
                                ]
                             =: ite (x .<= y)
                                    (nonDecreasing (merge xs (y .: ys)))
                                    (nonDecreasing (y .: merge (x .: xs) ys))
                             ?? [ hprf $ nonDecrIns `at` (Inst @"x" y, Inst @"ys" (merge (x .: xs) ys))
                                , hyp  $ nonDecreasing (x .: xs)
                                , hyp  $ nonDecreasing (y .: ys)
                                ]
                             =: ite (x .<= y)
                                    (nonDecreasing (merge xs (y .: ys)))
                                    (nonDecreasing (merge (x .: xs) ys))
                             ?? [ hprf $ ih          `at` (Inst @"xs" xs, Inst @"ys" (y .: ys))
                                , hprf $ nonDecrTail `at` (Inst @"x" x,   Inst @"xs" xs)
                                , hyp  $ nonDecreasing (y .: ys)
                                , hyp  $ nonDecreasing (x .: xs)
                                ]
                             =: ite (x .<= y)
                                    sTrue
                                    (nonDecreasing (merge (x .: xs) ys))
                             ?? [ hprf $ ih          `at` (Inst @"xs" (x .: xs), Inst @"ys" ys)
                                , hprf $ nonDecrTail `at` (Inst @"x"  y,         Inst @"xs" ys)
                                , hyp  $ nonDecreasing (y .: ys)
                                , hyp  $ nonDecreasing (x .: xs)
                                ]
                             =: ite (x .<= y) sTrue sTrue
                             ?? "simplify"
                             =: sTrue
                             =: qed

    sortNonDecreasing <-
        sInduct "sortNonDecreasing"
                (\(Forall @"xs" xs) -> nonDecreasing (mergeSort xs)) $
                \ih x xs -> [] |- nonDecreasing (mergeSort (x .: xs))
                               ?? "unfold"
                               =: let (h1, h2) = splitAt (length (x .: xs) `sEDiv` 2) (x .: xs)
                               in nonDecreasing (ite (length (x .: xs) .<= 1)
                                                     (x .: xs)
                                                     (merge (mergeSort h1) (mergeSort h2)))
                               ?? "push nonDecreasing down"
                               =: ite (length (x .: xs) .<= 1)
                                      (nonDecreasing (x .: xs))
                                      (nonDecreasing (merge (mergeSort h1) (mergeSort h2)))
                               ?? ih `at` (Inst @"xs" xs)
                               =: ite (length (x .: xs) .<= 1)
                                      sTrue
                                      (nonDecreasing (merge (mergeSort h1) (mergeSort h2)))
                               ?? [ ih `at` (Inst @"xs" h1)
                                  , ih `at` (Inst @"xs" h2)
                                  , mergeKeepsSort `at` (Inst @"xs" (mergeSort h1), Inst @"ys" (mergeSort h2))
                                  ]
                               =: sTrue
                               =: qed

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
