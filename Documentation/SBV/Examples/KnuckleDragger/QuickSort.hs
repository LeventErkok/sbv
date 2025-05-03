-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.QuickSort
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving quick sort correct.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.QuickSort where

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

import Prelude hiding (null, filter, (++), head, tail, length, all)
import Data.SBV.List

-- * Quick sort

-- | Quick-sort, using the first element as pivot.
quickSort :: SList Integer -> SList Integer
quickSort = smtFunction "quickSort" $ \l -> ite (null l)
                                                nil
                                                (let (x, xs) = uncons l
                                                 in    quickSort (filterLT x xs)
                                                    ++ singleton x
                                                    ++ quickSort (filterGE x xs))

-- | Filter all elements that are less than the first argument. Unfortunately we can't just define
-- this as @filter (.< e)@. Why? Because SBV firstifies higher-order calls, and the argument to these
-- functions would become free variables. This is currently not supported, hence the need for explicit definitions.
filterLT :: SInteger -> SList Integer -> SList Integer
filterLT = smtFunction "filterLT" $ \e l -> ite (null l)
                                                nil
                                                (let (x, xs) = uncons l
                                                     rest    = filterLT e xs
                                                 in ite (x .< e) (x .: rest) rest)

-- | Filter all elements that are greater than or equal to the first argument. Unfortunately we can't just define
-- this as @filter (.>= e)@ for the same reasons quoted above for 'filterLT.
filterGE :: SInteger -> SList Integer -> SList Integer
filterGE = smtFunction "filterMoreEq" $ \e l -> ite (null l)
                                                    nil
                                                    (let (x, xs) = uncons l
                                                         rest    = filterGE e xs
                                                     in ite (x .>= e) (x .: rest) rest)

-- * Helper functions

-- | A predicate testing whether a given list is non-decreasing.
nonDecreasing :: SList Integer -> SBool
nonDecreasing = smtFunction "nonDecreasing" $ \l ->  null l .|| null (tail l)
                                                 .|| let (x, l') = uncons l
                                                         (y, _)  = uncons l'
                                                     in x .<= y .&& nonDecreasing l'

-- | Is the given value less than or equal to all the elements in the list?
leAll :: SInteger -> SList Integer -> SBool
leAll = smtFunction "leAll" $ \e l -> null l .|| e .<= head l .&& leAll e (tail l)

-- | Is the given value greater than all the elements in the list?
gtAll :: SInteger -> SList Integer -> SBool
gtAll = smtFunction "gtAll" $ \e l -> null l .|| e .>  head l .&& gtAll e (tail l)

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

-- | Correctness of quick-sort.
--
-- We have:
--
-- >>> correctness
correctness :: IO Proof
correctness = runKDWith z3{kdOptions = (kdOptions z3) {ribbonLength = 60}} $ do

    --------------------------------------------------------------------------------------------
    -- Part I. Prove that the output of quick sort is non-decreasing.
    --------------------------------------------------------------------------------------------

    _onDecreasingCons <-
        lemma "nonDecreasingCons"
              (\(Forall @"xs" xs) (Forall @"e" e) ->
                 nonDecreasing xs .&& leAll e xs .=> nonDecreasing (singleton e ++ xs))
              []

    _onDecreasingApp <-
        lemma "nonDecreasingApp"
              (\(Forall @"xs" xs) (Forall @"ys" ys) ->
                  nonDecreasing xs .&& nonDecreasing ys .&& sNot (null ys) .&& gtAll (head ys) xs .=> nonDecreasing (xs ++ ys))
              [sorry]

    filterLTWorks <-
        lemma "filterLTWorks"
               (\(Forall @"e" e) (Forall @"l" l) -> gtAll e (quickSort (filterLT e l)))
               [sorry]

    filterGEWorks <-
        lemma "filterGEWorks"
               (\(Forall @"e" e) (Forall @"l" l) -> leAll e (quickSort (filterGE e l)))
               [sorry]

    filterLTShorter <-
        lemma "filterLTShorter"
              (\(Forall @"xs" xs) (Forall @"x" x) -> length (filterLT x xs) .< length (x .: xs))
              [sorry]

    filterGEShorter <-
        lemma "filterGEShorter"
              (\(Forall @"xs" xs) (Forall @"x" x) -> length (filterGE x xs) .< length (x .: xs))
              [sorry]

    nonDecreasingJoin <-
        lemma "nonDecreasingJoin"
              (\(Forall @"xs" xs) (Forall @"e" e) (Forall @"ys" ys) ->
                 nonDecreasing xs .&& gtAll e xs .&& leAll e ys .&& nonDecreasing ys .=>
                    nonDecreasing (xs ++ singleton e ++ ys))
              [sorry]

    quickSortKeepsSize <-
        lemma "quickSortKeepsSize"
              (\(Forall @"l" l) -> length (quickSort l) .== length l)
              [sorry]

    sortNonDecreasing <-
        sInductWith cvc5 "sortNonDecreasing"
                (\(Forall @"l" l) -> nonDecreasing (quickSort l))
                (length @Integer) $
                \ih l -> [] |-
                     split l trivial
                           (\x xs -> nonDecreasing (quickSort (x .: xs))
                                  ?? "unfold"
                                  =: let left  = quickSort (filterLT x xs)
                                         right = quickSort (filterGE x xs)
                                  in nonDecreasing (left ++ singleton x ++ right)
                                  ?? [ hprf $ ih                 `at`  Inst @"l" (filterLT x xs)
                                     , hprf $ ih                 `at`  Inst @"l" (filterGE x xs)
                                     , hprf $ quickSortKeepsSize `at` (Inst @"l" (filterLT x xs))
                                     , hprf $ quickSortKeepsSize `at` (Inst @"l" (filterGE x xs))
                                     , hprf $ filterLTWorks      `at` (Inst @"e" x, Inst @"l" xs)
                                     , hprf $ filterGEWorks      `at` (Inst @"e" x, Inst @"l" xs)
                                     , hprf $ filterLTShorter    `at` (Inst @"xs" xs, Inst @"x" x)
                                     , hprf $ filterGEShorter    `at` (Inst @"xs" xs, Inst @"x" x)
                                     , hprf $ nonDecreasingJoin  `at` (Inst @"xs" left, Inst @"e" x, Inst @"ys" right)
                                     ]
                                  =: sTrue
                                  =: qed)

    --------------------------------------------------------------------------------------------
    -- Part II. Prove that the output of quick sort is a permuation of its input
    --------------------------------------------------------------------------------------------

    sortIsPermutation <-
        sInductWith cvc5 "sortIsPermutation"
                (\(Forall @"l" l) (Forall @"e" e) -> count e l .== count e (quickSort l))
                (\(l :: SList Integer) (_e :: SInteger) -> length l) $
                \_h l e -> [] |- split l trivial
                                       (\x xs -> count e (quickSort (x .: xs))
                                              ?? "unfold"
                                              =: count e (x .: xs)
                                              =: qed)

    --------------------------------------------------------------------------------------------
    -- Put the two parts together for the final proof
    --------------------------------------------------------------------------------------------
    lemma "quickSortIsCorrect"
          (\(Forall @"xs" xs) -> let out = quickSort xs in nonDecreasing out .&& isPermutation xs out)
          [sortNonDecreasing, sortIsPermutation]
