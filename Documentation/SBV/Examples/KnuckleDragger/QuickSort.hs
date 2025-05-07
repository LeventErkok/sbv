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

module Documentation.SBV.Examples.KnuckleDragger.QuickSort(correctness) where

import Prelude hiding (null, (++), head, tail, elem, notElem, fst, length)

import Data.SBV
import Data.SBV.List hiding (partition)
import Data.SBV.Tuple
import Data.SBV.Tools.KnuckleDragger

-- * Quick sort

-- | Quick-sort, using the first element as pivot.
quickSort :: SList Integer -> SList Integer
quickSort = smtFunction "quickSort" $ \l -> ite (null l)
                                                nil
                                                (let (x,  xs) = uncons l
                                                     (lo, hi) = untuple (partition x xs)
                                                 in  quickSort lo ++ singleton x ++ quickSort hi)

-- | We define @partition@ as an explicit function. Unfortunately, we can't just replace this
-- with @\pivot xs -> Data.List.SBV.partition (.< pivot) xs@ because that would create a firstified version of partition
-- with a free-variable captured, which isn't supported due to higher-order limitations in SMTLib.
partition :: SInteger -> SList Integer -> STuple [Integer] [Integer]
partition = smtFunction "split" $ \pivot xs -> ite (null xs)
                                                   (tuple (nil, nil))
                                                   (let (a,  as) = uncons xs
                                                        (lo, hi) = untuple (partition pivot as)
                                                    in ite (a .< pivot)
                                                           (tuple (a .: lo, hi))
                                                           (tuple (lo, a .: hi)))

-- * Helper functions

{-
-- | A predicate testing whether a given list is non-decreasing.
nonDecreasing :: SList Integer -> SBool
nonDecreasing = smtFunction "nonDecreasing" $ \l ->  null l .|| null (tail l)
                                                 .|| let (x, l') = uncons l
                                                         (y, _)  = uncons l'
                                                     in x .<= y .&& nonDecreasing l'
-}

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

{-
-- | Is the given value less than or equal to all the elements in the list?
leAll :: SInteger -> SList Integer -> SBool
leAll = smtFunction "leAll" $ \e l -> null l .|| e .<= head l .&& leAll e (tail l)

-- | Is the given value greater than all the elements in the list?
gtAll :: SInteger -> SList Integer -> SBool
gtAll = smtFunction "gtAll" $ \e l -> null l .|| e .>  head l .&& gtAll e (tail l)
-}

-- * Correctness proof

-- | Correctness of quick-sort.
--
-- We have:
--
-- >>> correctness
correctness :: IO Proof
correctness = runKDWith z3{kdOptions = (kdOptions z3) {ribbonLength = 60}} $ do

    --------------------------------------------------------------------------------------------
    -- Part I. Prove that the output of quick sort is a permutation of its input
    --------------------------------------------------------------------------------------------

    partitionSmaller <-
         lemma "partitionSmaller"
           (\(Forall @"xs" xs) (Forall @"x" x) -> let (lo, hi) = untuple (partition x xs)
                                                      lxxs     = length (x .: xs)
                                                  in length lo .< lxxs .&& length hi .< lxxs)
           [sorry]

    partitionPermutes <-
       lemma "partitionPermutes"
             (\(Forall @"xs" xs) (Forall @"x" x) (Forall @"e" e) ->
                    let (lo, hi) = untuple (partition x xs)
                    in count e (x .: xs) .== count e lo + count e (singleton x) + count e hi)
             [sorry]

    sortEltCount <-
        sInductWith cvc5 "sortEltCount"
           (\(Forall @"l" l) (Forall @"e" e) -> count e (quickSort l) .== count e l)
           (\l (_ :: SInteger) -> length @Integer l) $
           \ih l e -> [] |- count e (quickSort l)
                         =: split l trivial
                                  (\x xs -> let (lo, hi) = untuple (partition x xs)
                                         in count e (quickSort lo ++ singleton x ++ quickSort hi)
                                         ?? sorry
                                         =: count e (quickSort lo) + count e (singleton x) + count e (quickSort hi)
                                         ?? [ ih               `at` (Inst @"l" lo,  Inst @"e" e)
                                            , ih               `at` (Inst @"l" hi,  Inst @"e" e)
                                            , partitionSmaller `at` (Inst @"xs" xs, Inst @"x" x)
                                            ]
                                         =: count e lo + count e (singleton x) + count e hi
                                         ?? partitionPermutes `at` (Inst @"xs" xs, Inst @"x" x, Inst @"e" e)
                                         =: count e l
                                         =: qed)

    sortIsPermutation <- lemma "sortIsPermutation" (\(Forall @"l" l) -> isPermutation l (quickSort l)) [sortEltCount]

    error "stop" sortIsPermutation
