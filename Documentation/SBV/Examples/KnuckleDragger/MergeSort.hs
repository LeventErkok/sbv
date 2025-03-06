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

import Prelude hiding (null, tail, length, elem, splitAt)
import Data.SBV.List

-- * Merge sort

-- | Merge two lists, assuming they're already sorted.
merge :: SList Integer -> SList Integer -> SList Integer
merge = smtFunction "merge" $ \xs ys -> ite (null xs) ys
                                      $ ite (null ys) xs
                                      $ let (a, as) = uncons xs
                                            (b, bs) = uncons ys
                                        in ite (a .<= b)
                                               (a .: merge as ys)
                                               (b .: merge xs bs)

-- | Merge sort, using 'merge' above to successively sort sublists and combine
mergeSort :: SList Integer -> SList Integer
mergeSort = smtFunction "mergeSort" $ \l -> ite (null l .|| null (tail l)) l
                                          $ let (f, s) = splitAt (length l `sDiv` 2) l
                                            in mergeSort f `merge` mergeSort s

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

    _onDecrTail <- lemma "nonDecTail"
                         (\(Forall @"x" x) (Forall @"xs" xs) -> nonDecreasing (x .: xs) .=> nonDecreasing xs)
                         []

    mergeNonDecreasing <-
        inductWith cvc5 "insertNonDecreasing"
               (\(Forall @"xs" xs) (Forall @"ys" ys) -> nonDecreasing xs .&& nonDecreasing ys .=> nonDecreasing (xs `merge` ys)) $
               \_h x xs y ys -> [nonDecreasing (x .: xs), nonDecreasing (y .: ys)]
                             |- nonDecreasing ((x .: xs) `merge` (y .: ys))
                             ?? "unfold merge"
                             =: nonDecreasing (ite (x .<= y)
                                                   (x .: merge xs (y .: ys))
                                                   (y .: merge (x .: xs) ys))
                             ?? "push nonDecreasing over the ite"
                             =: ite (x .<= y)
                                    (nonDecreasing (x .: merge xs (y .: ys)))
                                    (nonDecreasing (y .: merge (x .: xs) ys))
                             =: qed

    pure mergeNonDecreasing
