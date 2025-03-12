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

import Prelude hiding (null, length, head, tail, elem, splitAt, (++), take, drop)
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

-- | Count the number of occurrences of an element in a list
count :: SInteger -> SList Integer -> SInteger
count = smtFunction "count" $ \e l -> ite (null l)
                                          0
                                          (let (x, xs) = uncons l
                                               cxs     = count e xs
                                           in ite (e .== x) (1 + cxs) cxs)

-- | Are two lists permutations of each other?
isPermutation :: SList Integer -> SList Integer -> SBool
isPermutation xs ys = quantifiedBool (\(Forall @"x" x) -> count x xs .== count x ys)

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

    mergeCount <-
        sInduct "mergeCount"
                (\(Forall @"xs" xs) (Forall @"ys" ys) (Forall @"e" e) -> count e (merge xs ys) .== count e xs + count e ys) $
                \ih x xs y ys e -> [] |- count e (merge (x .: xs) (y .: ys))
                                      ?? "unfold merge"
                                      =: count e (ite (x .<= y)
                                                      (x .: merge xs (y .: ys))
                                                      (y .: merge (x .: xs) ys))
                                      ?? "push count inside"
                                      =: ite (x .<= y)
                                             (count e (x .: merge xs (y .: ys)))
                                             (count e (y .: merge (x .: xs) ys))
                                      ?? "unfold count, twice"
                                      =: ite (x .<= y)
                                             (let r = count e (merge xs (y .: ys)) in ite (e .== x) (1+r) r)
                                             (let r = count e (merge (x .: xs) ys) in ite (e .== y) (1+r) r)
                                      ?? ih `at` (Inst @"xs" xs, Inst @"ys" (y .: ys), Inst @"e" e)
                                      =: ite (x .<= y)
                                             (let r = count e xs + count e (y .: ys) in ite (e .== x) (1+r) r)
                                             (let r = count e (merge (x .: xs) ys) in ite (e .== y) (1+r) r)
                                      ?? ih `at` (Inst @"xs" (x .: xs), Inst @"ys" ys, Inst @"e" e)
                                      =: ite (x .<= y)
                                             (let r = count e xs + count e (y .: ys) in ite (e .== x) (1+r) r)
                                             (let r = count e (x .: xs) + count e ys in ite (e .== y) (1+r) r)
                                      ?? "unfold count in reverse, twice"
                                      =: ite (x .<= y)
                                             (count e (x .: xs) + count e (y .: ys))
                                             (count e (x .: xs) + count e (y .: ys))
                                      ?? "simplify"
                                      =: count e (x .: xs) + count e (y .: ys)
                                      =: qed

    countAppend <-
      induct "countAppend"
             (\(Forall @"xs" xs) (Forall @"ys" ys) (Forall @"e" e) -> count e (xs ++ ys) .== count e xs + count e ys) $
             \ih x xs ys e -> [] |- count e ((x .: xs) ++ ys)
                                 =: count e (x .: (xs ++ ys))
                                 ?? "unfold count"
                                 =: (let r = count e (xs ++ ys) in ite (e .== x) (1+r) r)
                                 ?? ih
                                 =: (let r = count e xs + count e ys in ite (e .== x) (1+r) r)
                                 ?? "simplify"
                                 =: count e (x .: xs) + count e ys
                                 =: qed

    takeDropCount <- do

       takeDrop <- lemma "take_drop"
                         (\(Forall @"n" n) (Forall @"xs" (xs :: SList Integer)) -> take n xs ++ drop n xs .== xs)
                         []

       calc "takeDropCount"
            (\(Forall @"xs" xs) (Forall @"n" n) (Forall @"e" e) -> count e (take n xs) + count e (drop n xs) .== count e xs) $
            \xs n e -> [] |- count e (take n xs) + count e (drop n xs)
                          ?? countAppend `at` (Inst @"xs" (take n xs), Inst @"ys" (drop n xs), Inst @"e" e)
                          =: count e (take n xs ++ drop n xs)
                          ?? takeDrop
                          =: count e xs
                          =: qed

    sortIsPermutation <-
        sInduct "sortIsPermutation"
                (\(Forall @"xs" xs) (Forall @"e" e) -> count e xs .== count e (mergeSort xs)) $
                \_h x xs e -> [] |- count e (x .: xs) .== count e (mergeSort (x .: xs))
                                 ?? "unfold"
                                 =: ite (e .== x) (1 + count e xs) (count e xs) .== count e (mergeSort (x .: xs))
                                 ?? [mergeCount, takeDropCount, sorry]
                                 =: sTrue
                                 =: qed

    --------------------------------------------------------------------------------------------
    -- Put the two parts together for the final proof
    --------------------------------------------------------------------------------------------
    lemma "mergeSortIsCorrect"
          (\(Forall @"xs" xs) -> let out = mergeSort xs in nonDecreasing out .&& isPermutation xs out)
          [sortNonDecreasing, sortIsPermutation]
