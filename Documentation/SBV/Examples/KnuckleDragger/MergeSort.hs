-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.MergeSort
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving merge sort correct.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeAbstractions    #-}
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
-- Lemma: nonDecrInsert                                        Q.E.D.
-- Inductive lemma (strong): mergeKeepsSort
--   Step: Measure is non-negative                             Q.E.D.
--   Step: 1 (4 way full case split)
--     Step: 1.1                                               Q.E.D.
--     Step: 1.2                                               Q.E.D.
--     Step: 1.3                                               Q.E.D.
--     Step: 1.4.1 (unfold merge)                              Q.E.D.
--     Step: 1.4.2 (2 way case split)
--       Step: 1.4.2.1.1 (case split)                          Q.E.D.
--       Step: 1.4.2.1.2                                       Q.E.D.
--       Step: 1.4.2.2.1 (case split)                          Q.E.D.
--       Step: 1.4.2.2.2                                       Q.E.D.
--       Step: 1.4.2.Completeness                              Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma (strong): sortNonDecreasing
--   Step: Measure is non-negative                             Q.E.D.
--   Step: 1 (2 way full case split)
--     Step: 1.1                                               Q.E.D.
--     Step: 1.2.1 (unfold)                                    Q.E.D.
--     Step: 1.2.2 (push nonDecreasing down)                   Q.E.D.
--     Step: 1.2.3                                             Q.E.D.
--     Step: 1.2.4                                             Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma (strong): mergeCount
--   Step: Measure is non-negative                             Q.E.D.
--   Step: 1 (4 way full case split)
--     Step: 1.1                                               Q.E.D.
--     Step: 1.2                                               Q.E.D.
--     Step: 1.3                                               Q.E.D.
--     Step: 1.4.1 (unfold merge)                              Q.E.D.
--     Step: 1.4.2 (push count inside)                         Q.E.D.
--     Step: 1.4.3 (unfold count, twice)                       Q.E.D.
--     Step: 1.4.4                                             Q.E.D.
--     Step: 1.4.5                                             Q.E.D.
--     Step: 1.4.6 (unfold count in reverse, twice)            Q.E.D.
--     Step: 1.4.7 (simplify)                                  Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma: countAppend
--   Step: Base                                                Q.E.D.
--   Step: 1                                                   Q.E.D.
--   Step: 2 (unfold count)                                    Q.E.D.
--   Step: 3                                                   Q.E.D.
--   Step: 4 (simplify)                                        Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: take_drop                                            Q.E.D.
-- Lemma: takeDropCount
--   Step: 1                                                   Q.E.D.
--   Step: 2                                                   Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma (strong): sortIsPermutation
--   Step: Measure is non-negative                             Q.E.D.
--   Step: 1 (2 way full case split)
--     Step: 1.1                                               Q.E.D.
--     Step: 1.2.1 (unfold mergeSort)                          Q.E.D.
--     Step: 1.2.2 (push count down, simplify, rearrange)      Q.E.D.
--     Step: 1.2.3                                             Q.E.D.
--     Step: 1.2.4                                             Q.E.D.
--     Step: 1.2.5                                             Q.E.D.
--     Step: 1.2.6                                             Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: mergeSortIsCorrect                                   Q.E.D.
-- [Proven] mergeSortIsCorrect
correctness :: IO Proof
correctness = runKDWith z3{kdOptions = (kdOptions z3) {ribbonLength = 60}} $ do

    --------------------------------------------------------------------------------------------
    -- Part I. Prove that the output of merge sort is non-decreasing.
    --------------------------------------------------------------------------------------------

    nonDecrIns <- lemma "nonDecrInsert"
                        (\(Forall @"x" x) (Forall @"ys" ys) -> nonDecreasing ys .&& sNot (null ys) .&& x .<= head ys
                                                           .=> nonDecreasing (x .: ys))
                        []

    mergeKeepsSort <-
        sInductWith cvc5 "mergeKeepsSort"
           (\(Forall @"xs" xs) (Forall @"ys" ys) -> nonDecreasing xs .&& nonDecreasing ys .=> nonDecreasing (merge xs ys))
           (\(xs :: SList Integer) (ys :: SList Integer) -> (length xs, length ys)) $
           \ih xs ys -> [nonDecreasing xs, nonDecreasing ys]
                     |- split2 (xs, ys)
                               trivial           -- when both xs and ys are empty.  Trivial.
                               trivial           -- when xs is empty, but ys isn't. Trivial.
                               trivial           -- when ys is empty, but xs isn't. Trivial.
                               (\(a, as) (b, bs) ->
                                     nonDecreasing (merge (a .: as) (b .: bs))
                                  ?? "unfold merge"
                                  =: nonDecreasing (ite (a .<= b)
                                                        (a .: merge as (b .: bs))
                                                        (b .: merge (a .: as) bs))
                                  ?? "case split"
                                  =: cases [ a .<= b ==> nonDecreasing (a .: merge as (b .: bs))
                                                      ?? [ hprf $ ih         `at` (Inst @"xs" as, Inst @"ys" (b .: bs))
                                                         , hprf $ nonDecrIns `at` (Inst @"x" a, Inst @"ys" (merge as (b .: bs)))
                                                         , hasm $ nonDecreasing (a .: as)
                                                         , hasm $ nonDecreasing (b .: bs)
                                                         ]
                                                      =: sTrue
                                                      =: qed
                                           , a .> b  ==> nonDecreasing (b .: merge (a .: as) bs)
                                                      ?? [ hprf $ ih         `at` (Inst @"xs" (a .: as), Inst @"ys" bs)
                                                         , hprf $ nonDecrIns `at` (Inst @"x" b, Inst @"ys" (merge (a .: as) bs))
                                                         , hasm $ nonDecreasing (a .: as)
                                                         , hasm $ nonDecreasing (b .: bs)
                                                         ]
                                                      =: sTrue
                                                      =: qed
                                           ])

    sortNonDecreasing <-
        sInduct "sortNonDecreasing"
                (\(Forall @"xs" xs) -> nonDecreasing (mergeSort xs))
                (length @Integer) $
                \ih xs -> [] |- split xs
                                      qed
                                      (\e es -> nonDecreasing (mergeSort (e .: es))
                                             ?? "unfold"
                                             =: let (h1, h2) = splitAt (length (e .: es) `sEDiv` 2) (e .: es)
                                                in nonDecreasing (ite (length (e .: es) .<= 1)
                                                                      (e .: es)
                                                                      (merge (mergeSort h1) (mergeSort h2)))
                                             ?? "push nonDecreasing down"
                                             =: ite (length (e .: es) .<= 1)
                                                    (nonDecreasing (e .: es))
                                                    (nonDecreasing (merge (mergeSort h1) (mergeSort h2)))
                                             ?? ih `at` Inst @"xs" es
                                             =: ite (length (e .: es) .<= 1)
                                                    sTrue
                                                    (nonDecreasing (merge (mergeSort h1) (mergeSort h2)))
                                             ?? [ ih `at` Inst @"xs" h1
                                                , ih `at` Inst @"xs" h2
                                                , mergeKeepsSort `at` (Inst @"xs" (mergeSort h1), Inst @"ys" (mergeSort h2))
                                                ]
                                             =: sTrue
                                             =: qed)

    --------------------------------------------------------------------------------------------
    -- Part II. Prove that the output of merge sort is a permuation of its input
    --------------------------------------------------------------------------------------------
    mergeCount <-
        sInduct "mergeCount"
                (\(Forall @"xs" xs) (Forall @"ys" ys) (Forall @"e" e) -> count e (merge xs ys) .== count e xs + count e ys)
                (\(xs :: SList Integer) (ys :: SList Integer) (_e :: SInteger) -> (length xs, length ys)) $
                \ih as bs e -> [] |-
                        split2 (as, bs)
                               trivial
                               trivial
                               trivial
                               (\(x, xs) (y, ys) -> count e (merge (x .: xs) (y .: ys))
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
                                                 =: qed)

    countAppend <-
      induct "countAppend"
             (\(Forall @"xs" xs) (Forall @"ys" ys) (Forall @"e" e) -> count e (xs ++ ys) .== count e xs + count e ys) $
             \ih x xs ys e -> [] |- count e ((x .: xs) ++ ys)
                                 =: count e (x .: (xs ++ ys))
                                 ?? "unfold count"
                                 =: (let r = count e (xs ++ ys) in ite (e .== x) (1+r) r)
                                 ?? ih `at` (Inst @"ys" ys, Inst @"e" e)
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
        sInductWith cvc5 "sortIsPermutation"
                (\(Forall @"xs" xs) (Forall @"e" e) -> count e xs .== count e (mergeSort xs))
                (\(xs :: SList Integer) (_e :: SInteger) -> length xs) $
                \ih as e -> [] |- split as
                                        qed
                                        (\x xs -> count e (mergeSort (x .: xs))
                                               ?? "unfold mergeSort"
                                               =: count e (ite (length (x .: xs) .<= 1)
                                                               (x .: xs)
                                                               (let (h1, h2) = splitAt (length (x .: xs) `sEDiv` 2) (x .: xs)
                                                                in merge (mergeSort h1) (mergeSort h2)))
                                               ?? "push count down, simplify, rearrange"
                                               =: let (h1, h2) = splitAt (length (x .: xs) `sEDiv` 2) (x .: xs)
                                               in ite (null xs)
                                                      (count e (singleton x))
                                                      (count e (merge (mergeSort h1) (mergeSort h2)))
                                               ?? mergeCount `at` (Inst @"xs" (mergeSort h1), Inst @"ys" (mergeSort h2), Inst @"e" e)
                                               =: ite (null xs)
                                                      (count e (singleton x))
                                                      (count e (mergeSort h1) + count e (mergeSort h2))
                                               ?? [ hprf  (ih `at` (Inst @"xs" h1, Inst @"e" e))
                                                  , hasm  (length h1 .< length (x .: xs))
                                                  ]
                                               =: ite (null xs)
                                                      (count e (singleton x))
                                                      (count e h1 + count e (mergeSort h2))
                                               ?? ih `at` (Inst @"xs" h2, Inst @"e" e)
                                               =: ite (null xs)
                                                      (count e (singleton x))
                                                      (count e h1 + count e h2)
                                               ?? takeDropCount `at` (Inst @"xs" (x .: xs), Inst @"n" (length (x .: xs) `sEDiv` 2), Inst @"e" e)
                                               =: ite (null xs)
                                                      (count e (singleton x))
                                                      (count e (x .: xs))
                                               =: qed)

    --------------------------------------------------------------------------------------------
    -- Put the two parts together for the final proof
    --------------------------------------------------------------------------------------------
    lemma "mergeSortIsCorrect"
          (\(Forall @"xs" xs) -> let out = mergeSort xs in nonDecreasing out .&& isPermutation xs out)
          [sortNonDecreasing, sortIsPermutation]
