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
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.MergeSort where

import Prelude hiding (null, length, head, tail, elem, splitAt, (++), take, drop)

import Data.SBV
import Data.SBV.List
import Data.SBV.Tuple
import Data.SBV.TP

import qualified Documentation.SBV.Examples.TP.Lists       as TP
import qualified Documentation.SBV.Examples.TP.SortHelpers as SH

#ifdef DOCTEST
-- $setup
-- >>> :set -XTypeApplications
#endif

-- * Merge sort

-- | Merge two already sorted lists into another
merge :: (OrdSymbolic (SBV a), SymVal a) => SList a -> SList a -> SList a
merge = smtFunction "merge"
      $ \l r -> [sCase| tuple (l, r) of
                   ([], _) -> r
                   (_, []) -> l

                   (ll@(a : as), rr@(b : bs)) | a .<= b -> a .: merge as rr
                                              | True    -> b .: merge ll bs
                |]

-- | Merge sort, using 'merge' above to successively sort halved input
mergeSort :: (OrdSymbolic (SBV a), SymVal a) => SList a -> SList a
mergeSort = smtFunction "mergeSort"
          $ \l -> [sCase| l of
                     []  -> l
                     [_] -> l
                     _   -> let (h1, h2) = splitAt (length l `sEDiv` 2) l
                            in merge (mergeSort h1) (mergeSort h2)
                  |]

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
-- Lemma: countOneStep                                         Q.E.D.
-- Lemma: mergeHead                                            Q.E.D.
-- Lemma: mergeUnfold                                          Q.E.D.
-- Inductive lemma (strong): mergeKeepsSort
--   Step: Measure is non-negative                             Q.E.D.
--   Step: 1 (3 way case split)
--     Step: 1.1                                               Q.E.D.
--     Step: 1.2                                               Q.E.D.
--     Step: 1.3 (2 way case split)
--       Step: 1.3.1.1 (2 way case split)                      Q.E.D.
--       Step: 1.3.1.2                                         Q.E.D.
--       Step: 1.3.1.3                                         Q.E.D.
--       Step: 1.3.2.1 (2 way case split)                      Q.E.D.
--       Step: 1.3.2.2                                         Q.E.D.
--       Step: 1.3.2.3                                         Q.E.D.
--       Step: 1.3.Completeness                                Q.E.D.
--     Step: 1.Completeness                                    Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma (strong): sortNonDecreasing
--   Step: Measure is non-negative                             Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                               Q.E.D.
--     Step: 1.2.1 (unfold)                                    Q.E.D.
--     Step: 1.2.2 (push nonDecreasing down)                   Q.E.D.
--     Step: 1.2.3                                             Q.E.D.
--     Step: 1.2.4                                             Q.E.D.
--     Step: 1.Completeness                                    Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma (strong): mergeCount
--   Step: Measure is non-negative                             Q.E.D.
--   Step: 1 (3 way case split)
--     Step: 1.1                                               Q.E.D.
--     Step: 1.2                                               Q.E.D.
--     Step: 1.3.1 (unfold merge)                              Q.E.D.
--     Step: 1.3.2 (push count inside)                         Q.E.D.
--     Step: 1.3.3 (unfold count, twice)                       Q.E.D.
--     Step: 1.3.4                                             Q.E.D.
--     Step: 1.3.5                                             Q.E.D.
--     Step: 1.3.6 (unfold count in reverse, twice)            Q.E.D.
--     Step: 1.3.7 (simplify)                                  Q.E.D.
--     Step: 1.Completeness                                    Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma (strong): sortIsPermutation
--   Step: Measure is non-negative                             Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                               Q.E.D.
--     Step: 1.2.1 (unfold mergeSort)                          Q.E.D.
--     Step: 1.2.2 (push count down, simplify, rearrange)      Q.E.D.
--     Step: 1.2.3                                             Q.E.D.
--     Step: 1.2.4                                             Q.E.D.
--     Step: 1.2.5                                             Q.E.D.
--     Step: 1.2.6                                             Q.E.D.
--     Step: 1.Completeness                                    Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: mergeSortIsCorrect                                   Q.E.D.
-- Functions proven terminating: count, merge, mergeSort, nonDecreasing
-- [Proven] mergeSortIsCorrect :: Ɐxs ∷ [Integer] → Bool
correctness :: forall a. (OrdSymbolic (SBV a), SymVal a) => IO (Proof (Forall "xs" [a] -> SBool))
correctness = runTP $ do

    --------------------------------------------------------------------------------------------
    -- Part I. Import helper lemmas, definitions
    --------------------------------------------------------------------------------------------
    let nonDecreasing = SH.nonDecreasing @a
        isPermutation = SH.isPermutation @a
        count         = TP.count         @a

    nonDecrIns    <- SH.nonDecrIns    @a
    takeDropCount <- TP.takeDropCount @a
    cntStep       <- TP.countOneStep  @a

    -- Head of merge: one unfold of merge suffices for the solver
    mergeHead <- lemma "mergeHead"
                    (\(Forall xs) (Forall ys) -> sNot (null ys) .=>
                        head (merge xs ys) .== ite (null xs) (head ys) (ite (head xs .<= head ys) (head xs) (head ys)))
                    []

    -- Unfold lemma for merge's recursive case
    mergeUnfold <- lemma "mergeUnfold"
                    (\(Forall x) (Forall xs) (Forall y) (Forall ys) ->
                        merge (x .: xs) (y .: ys) .== ite (x .<= y) (x .: merge xs (y .: ys)) (y .: merge (x .: xs) ys))
                    []

    --------------------------------------------------------------------------------------------
    -- Part II. Prove that the output of merge sort is non-decreasing.
    --------------------------------------------------------------------------------------------

    mergeKeepsSort <-
        sInductWith cvc5 "mergeKeepsSort"
           (\(Forall xs) (Forall ys) -> nonDecreasing xs .&& nonDecreasing ys .=> nonDecreasing (merge xs ys))
           (\xs ys -> tuple (length xs, length ys), []) $
           \ih xs ys -> [nonDecreasing xs, nonDecreasing ys]
                     |- [pCase| tuple (xs, ys) of
                          ([], _)          -> trivial
                          (_, [])          -> trivial
                          (ll@(a : as), rr@(b : bs)) ->
                                nonDecreasing (merge ll rr)
                             ?? "2 way case split"
                             =: cases [ a .<= b ==> nonDecreasing (merge ll rr)
                                                 ?? mergeUnfold `at` (Inst @"x" a, Inst @"xs" as, Inst @"y" b, Inst @"ys" bs)
                                                 =: nonDecreasing (a .: merge as rr)
                                                 ?? ih         `at` (Inst @"xs" as, Inst @"ys" rr)
                                                 ?? nonDecrIns `at` (Inst @"x" a, Inst @"xs" (merge as rr))
                                                 ?? mergeHead  `at` (Inst @"xs" as, Inst @"ys" rr)
                                                 =: sTrue
                                                 =: qed
                                      , a .> b  ==> nonDecreasing (merge ll rr)
                                                 ?? mergeUnfold `at` (Inst @"x" a, Inst @"xs" as, Inst @"y" b, Inst @"ys" bs)
                                                 =: nonDecreasing (b .: merge ll bs)
                                                 ?? ih         `at` (Inst @"xs" ll, Inst @"ys" bs)
                                                 ?? nonDecrIns `at` (Inst @"x" b, Inst @"xs" (merge ll bs))
                                                 ?? mergeHead  `at` (Inst @"xs" ll, Inst @"ys" bs)
                                                 =: sTrue
                                                 =: qed
                                      ]
                        |]

    sortNonDecreasing <-
        sInduct "sortNonDecreasing"
                (\(Forall xs) -> nonDecreasing (mergeSort xs))
                (length, []) $
                \ih xs -> [] |- [pCase| xs of
                                  []             -> qed
                                  whole@(_ : es) ->
                                        nonDecreasing (mergeSort whole)
                                     ?? "unfold"
                                     =: let (h1, h2) = splitAt (length whole `sEDiv` 2) whole
                                        in nonDecreasing (ite (length whole .<= 1)
                                                              whole
                                                              (merge (mergeSort h1) (mergeSort h2)))
                                     ?? "push nonDecreasing down"
                                     =: ite (length whole .<= 1)
                                            (nonDecreasing whole)
                                            (nonDecreasing (merge (mergeSort h1) (mergeSort h2)))
                                     ?? ih `at` Inst @"xs" es
                                     =: ite (length whole .<= 1)
                                            sTrue
                                            (nonDecreasing (merge (mergeSort h1) (mergeSort h2)))
                                     ?? ih `at` Inst @"xs" h1
                                     ?? ih `at` Inst @"xs" h2
                                     ?? mergeKeepsSort `at` (Inst @"xs" (mergeSort h1), Inst @"ys" (mergeSort h2))
                                     =: sTrue
                                     =: qed
                                |]

    --------------------------------------------------------------------------------------------
    -- Part III. Prove that the output of merge sort is a permuation of its input
    --------------------------------------------------------------------------------------------
    mergeCount <-
        sInduct "mergeCount"
                (\(Forall xs) (Forall ys) (Forall e) -> count e (merge xs ys) .== count e xs + count e ys)
                (\xs ys _e -> tuple (length xs, length ys), []) $
                \ih as bs e -> [] |- [pCase| tuple (as, bs) of
                                      ([], _) -> trivial
                                      (_, []) -> trivial

                                      (ll@(x : xs), rr@(y : ys)) ->
                                              count e (merge ll rr)
                                           ?? "unfold merge"
                                           =: count e (ite (x .<= y)
                                                           (x .: merge xs rr)
                                                           (y .: merge ll ys))
                                           ?? "push count inside"
                                           =: ite (x .<= y)
                                                  (count e (x .: merge xs rr))
                                                  (count e (y .: merge ll ys))
                                           ?? "unfold count, twice"
                                           ?? cntStep `at` (Inst @"e" e, Inst @"x" x, Inst @"xs" (merge xs rr))
                                           ?? cntStep `at` (Inst @"e" e, Inst @"x" y, Inst @"xs" (merge ll ys))
                                           =: ite (x .<= y)
                                                  (let r = count e (merge xs rr) in ite (e .== x) (1+r) r)
                                                  (let r = count e (merge ll ys) in ite (e .== y) (1+r) r)
                                           ?? ih `at` (Inst @"xs" xs, Inst @"ys" rr, Inst @"e" e)
                                           =: ite (x .<= y)
                                                  (let r = count e xs + count e rr in ite (e .== x) (1+r) r)
                                                  (let r = count e (merge ll ys) in ite (e .== y) (1+r) r)
                                           ?? ih `at` (Inst @"xs" ll, Inst @"ys" ys, Inst @"e" e)
                                           =: ite (x .<= y)
                                                  (let r = count e xs + count e rr in ite (e .== x) (1+r) r)
                                                  (let r = count e ll + count e ys in ite (e .== y) (1+r) r)
                                           ?? "unfold count in reverse, twice"
                                           ?? cntStep `at` (Inst @"e" e, Inst @"x" x, Inst @"xs" xs)
                                           ?? cntStep `at` (Inst @"e" e, Inst @"x" y, Inst @"xs" ys)
                                           =: ite (x .<= y)
                                                  (count e ll + count e rr)
                                                  (count e ll + count e rr)
                                           ?? "simplify"
                                           =: count e ll + count e rr
                                           =: qed
                                    |]

    sortIsPermutation <-
        sInductWith cvc5 "sortIsPermutation"
                (\(Forall xs) (Forall e) -> count e xs .== count e (mergeSort xs))
                (\xs _e -> length xs, []) $
                \ih as e -> [] |- [pCase| as of
                                    []     -> trivial
                                    whole@(x : xs) -> count e (mergeSort whole)
                                           ?? "unfold mergeSort"
                                           =: count e (ite (length whole .<= 1)
                                                           whole
                                                           (let (h1, h2) = splitAt (length whole `sEDiv` 2) whole
                                                            in merge (mergeSort h1) (mergeSort h2)))
                                           ?? "push count down, simplify, rearrange"
                                           =: let (h1, h2) = splitAt (length whole `sEDiv` 2) whole
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
                                           ?? takeDropCount `at` (Inst @"xs" whole, Inst @"n" (length whole `sEDiv` 2), Inst @"e" e)
                                           =: ite (null xs)
                                                  (count e [x])
                                                  (count e whole)
                                           =: qed
                                  |]

    --------------------------------------------------------------------------------------------
    -- Put the two parts together for the final proof
    --------------------------------------------------------------------------------------------
    lemma "mergeSortIsCorrect"
          (\(Forall xs) -> let out = mergeSort xs in nonDecreasing out .&& isPermutation xs out)
          [proofOf sortNonDecreasing, proofOf sortIsPermutation]
