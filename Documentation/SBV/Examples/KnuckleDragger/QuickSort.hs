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

import Prelude hiding (null, filter, (++), tail, length)
import Data.SBV.List

-- * Quick sort

-- | Quick-sort, using the first element as pivot.
quickSort :: SList Integer -> SList Integer
quickSort = smtFunction "quickSort" $ \l -> ite (null l)
                                                nil
                                                (let (x, xs) = uncons l
                                                 in filterLess x xs ++ singleton x ++ filterMoreEq x xs)

-- | Filter all elements that are less than the first argument. Unfortunately we can't just define
-- this as @filter (.< e)@. Why? Because SBV firstifies higher-order calls, and the argument to these
-- functions would become free variables. This is currently not supported, hence the need for explicit definitions.
filterLess :: SInteger -> SList Integer -> SList Integer
filterLess = smtFunction "filterLess" $ \e l -> ite (null l)
                                                    nil
                                                    (let (x, xs) = uncons l
                                                         rest    = filterLess e xs
                                                     in ite (e .< x) (e .: rest) rest)

-- | Filter all elements that are greater than or equal to the first argument. Unfortunately we can't just define
-- this as @filter (.>= e)@ for the same reasons quoted above for 'filterLess'.
filterMoreEq :: SInteger -> SList Integer -> SList Integer
filterMoreEq = smtFunction "filterMoreEq" $ \e l -> ite (null l)
                                                        nil
                                                        (let (x, xs) = uncons l
                                                             rest    = filterLess e xs
                                                         in ite (e .>= x) (e .: rest) rest)

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

    sortNonDecreasing <-
        sInduct "sortNonDecreasing"
                (\(Forall @"xs" xs) -> nonDecreasing (quickSort xs))
                (length @Integer) $
                \_h xs -> [] |- split xs
                                      qed
                                      (\e es -> nonDecreasing (quickSort (e .: es))
                                             ?? "unfold"
                                             =: sTrue
                                             =: qed)

    --------------------------------------------------------------------------------------------
    -- Part II. Prove that the output of quick sort is a permuation of its input
    --------------------------------------------------------------------------------------------

    sortIsPermutation <-
        sInductWith cvc5 "sortIsPermutation"
                (\(Forall @"xs" xs) (Forall @"e" e) -> count e xs .== count e (quickSort xs))
                (\(xs :: SList Integer) (_e :: SInteger) -> length xs) $
                \_h as e -> [] |- split as
                                        qed
                                        (\x xs -> count e (quickSort (x .: xs))
                                               ?? "unfold"
                                               =: qed)

    --------------------------------------------------------------------------------------------
    -- Put the two parts together for the final proof
    --------------------------------------------------------------------------------------------
    lemma "quickSortIsCorrect"
          (\(Forall @"xs" xs) -> let out = quickSort xs in nonDecreasing out .&& isPermutation xs out)
          [sortNonDecreasing, sortIsPermutation]
