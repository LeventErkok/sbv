-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.MergeSort
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving merge sort correct.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.MergeSort where

import Prelude hiding (null, length, head, tail, elem, splitAt, (++), take, drop)

import Data.SBV
import Data.SBV.List
import Data.SBV.Tuple
import Data.SBV.TP
import qualified Data.SBV.TP.List as TP

import qualified Documentation.SBV.Examples.TP.SortHelpers as SH

#ifdef DOCTEST
-- $setup
-- >>> :set -XTypeApplications
#endif

-- * Merge sort

-- | Merge two already sorted lists into another
merge :: (OrdSymbolic (SBV a), SymVal a) => SList a -> SList a -> SList a
merge = smtFunction "merge" $ \l r -> ite (null l) r
                                    $ ite (null r) l
                                    $ let (a, as) = uncons l
                                          (b, bs) = uncons r
                                      in ite (a .<= b) (a .: merge as r) (b .: merge l bs)

-- | Merge sort, using 'merge' above to successively sort halved input
mergeSort :: (OrdSymbolic (SBV a), SymVal a) => SList a -> SList a
mergeSort = smtFunction "mergeSort" $ \l -> ite (length l .<= 1) l
                                              $ let (h1, h2) = splitAt (length l `sEDiv` 2) l
                                                in merge (mergeSort h1) (mergeSort h2)

-- * Correctness proof

-- | Correctness of merge-sort.
--
-- We have:
--
-- >>> correctness @Integer
-- Lemma: nonDecrInsert                                        Q.E.D.
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
-- [Proven] mergeSortIsCorrect :: Ɐxs ∷ [Integer] → Bool
correctness :: forall a. (OrdSymbolic (SBV a), SymVal a) => IO (Proof (Forall "xs" [a] -> SBool))
correctness = runTPWith (tpRibbon 60 z3) $ do

    --------------------------------------------------------------------------------------------
    -- Part I. Import helper lemmas, definitions
    --------------------------------------------------------------------------------------------
    let nonDecreasing = SH.nonDecreasing @a
        isPermutation = SH.isPermutation @a
        count         = TP.count         @a

    nonDecrIns    <- SH.nonDecrIns    @a
    takeDropCount <- TP.takeDropCount @a

    --------------------------------------------------------------------------------------------
    -- Part II. Prove that the output of merge sort is non-decreasing.
    --------------------------------------------------------------------------------------------

    mergeKeepsSort <-
        sInductWith cvc5 "mergeKeepsSort"
           (\(Forall xs) (Forall ys) -> nonDecreasing xs .&& nonDecreasing ys .=> nonDecreasing (merge xs ys))
           (\xs ys -> tuple (length xs, length ys)) $
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
                                                      ?? ih         `at` (Inst @"xs" as, Inst @"ys" (b .: bs))
                                                      ?? nonDecrIns `at` (Inst @"x" a, Inst @"xs" (merge as (b .: bs)))
                                                      =: sTrue
                                                      =: qed
                                           , a .> b  ==> nonDecreasing (b .: merge (a .: as) bs)
                                                      ?? ih         `at` (Inst @"xs" (a .: as), Inst @"ys" bs)
                                                      ?? nonDecrIns `at` (Inst @"x" b, Inst @"xs" (merge (a .: as) bs))
                                                      =: sTrue
                                                      =: qed
                                           ])

    sortNonDecreasing <-
        sInduct "sortNonDecreasing"
                (\(Forall xs) -> nonDecreasing (mergeSort xs))
                length $
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
                                             ?? ih `at` Inst @"xs" h1
                                             ?? ih `at` Inst @"xs" h2
                                             ?? mergeKeepsSort `at` (Inst @"xs" (mergeSort h1), Inst @"ys" (mergeSort h2))
                                             =: sTrue
                                             =: qed)

    --------------------------------------------------------------------------------------------
    -- Part III. Prove that the output of merge sort is a permuation of its input
    --------------------------------------------------------------------------------------------
    mergeCount <-
        sInduct "mergeCount"
                (\(Forall xs) (Forall ys) (Forall e) -> count e (merge xs ys) .== count e xs + count e ys)
                (\xs ys _e -> tuple (length xs, length ys)) $
                \ih as bs e -> [] |- split2 (as, bs)
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

    sortIsPermutation <-
        sInductWith cvc5 "sortIsPermutation"
                (\(Forall xs) (Forall e) -> count e xs .== count e (mergeSort xs))
                (\xs _e -> length xs) $
                \ih as e -> [] |- split as
                                        trivial
                                        (\x xs -> count e (mergeSort (x .: xs))
                                               ?? "unfold mergeSort"
                                               =: count e (ite (length (x .: xs) .<= 1)
                                                               (x .: xs)
                                                               (let (h1, h2) = splitAt (length (x .: xs) `sEDiv` 2) (x .: xs)
                                                                in merge (mergeSort h1) (mergeSort h2)))
                                               ?? "push count down, simplify, rearrange"
                                               =: let (h1, h2) = splitAt (length (x .: xs) `sEDiv` 2) (x .: xs)
                                               in ite (null xs)
                                                      (count e [x])
                                                      (count e (merge (mergeSort h1) (mergeSort h2)))
                                               ?? mergeCount `at` (Inst @"xs" (mergeSort h1), Inst @"ys" (mergeSort h2), Inst @"e" e)
                                               =: ite (null xs)
                                                      (count e [x])
                                                      (count e (mergeSort h1) + count e (mergeSort h2))
                                               ?? ih `at` (Inst @"xs" h1, Inst @"e" e)
                                               =: ite (null xs)
                                                      (count e [x])
                                                      (count e h1 + count e (mergeSort h2))
                                               ?? ih `at` (Inst @"xs" h2, Inst @"e" e)
                                               =: ite (null xs)
                                                      (count e [x])
                                                      (count e h1 + count e h2)
                                               ?? takeDropCount `at` (Inst @"xs" (x .: xs), Inst @"n" (length (x .: xs) `sEDiv` 2), Inst @"e" e)
                                               =: ite (null xs)
                                                      (count e [x])
                                                      (count e (x .: xs))
                                               =: qed)

    --------------------------------------------------------------------------------------------
    -- Put the two parts together for the final proof
    --------------------------------------------------------------------------------------------
    lemma "mergeSortIsCorrect"
          (\(Forall xs) -> let out = mergeSort xs in nonDecreasing out .&& isPermutation xs out)
          [proofOf sortNonDecreasing, proofOf sortIsPermutation]
