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

-- | Is the given value less than or equal to all the elements in the list?
leAll :: SInteger -> SList Integer -> SBool
leAll = smtFunction "leAll" $ \e l -> null l .|| e .<= head l .&& leAll e (tail l)

-- | Is the given value greater than all the elements in the list?
gtAll :: SInteger -> SList Integer -> SBool
gtAll = smtFunction "gtAll" $ \e l -> null l .|| e .>  head l .&& gtAll e (tail l)

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

{-
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

    sortNonDecreasing <-
        sInductWith cvc5 "sortNonDecreasing"
                (\(Forall @"l" l) -> nonDecreasing (quickSort l))
                (length @Integer) $
                \_h l -> [] |-
                     split l trivial
                           (\x xs -> nonDecreasing (quickSort (x .: xs))
                                  ?? "unfold"
                                  =: let (lo, hi) = untuple (partition x xs)
                                  in nonDecreasing (quickSort lo ++ singleton x ++ quickSort hi)
                                  {-
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
                                  -}
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

    filterLTShorter <-
        lemma "filterLTShorter"
              (\(Forall @"xs" xs) (Forall @"x" x) -> length (filterLT x xs) .< length (x .: xs))
              [sorry]

    filterGEShorter <-
        lemma "filterGEShorter"
              (\(Forall @"xs" xs) (Forall @"x" x) -> length (filterGE x xs) .< length (x .: xs))
              [sorry]
-}

    partitionWorks <-
        lemma "partitionWorks"
              (\(Forall @"pivot" pivot) (Forall @"xs" xs) ->
                   let (lo, hi) = untuple (partition pivot xs)
                   in gtAll pivot lo .&& leAll pivot hi)
              [sorry]

    {-
    quickSortKeepsSize <-
        lemma "quickSortKeepsSize"
              (\(Forall @"l" l) -> length (quickSort l) .== length l)
              [sorry]
              -}

    nonDecreasingJoin <-
        lemma "nonDecreasingJoin"
              (\(Forall @"lo" lo) (Forall @"pivot" pivot) (Forall @"hi" hi) ->
                 nonDecreasing lo .&& gtAll pivot lo .&& leAll pivot hi .&& nonDecreasing hi .=>
                    nonDecreasing (lo ++ singleton pivot ++ hi))
              [sorry]

    helper1 <- lemma "helper1" (\(Forall @"pivot" pivot) (Forall @"xs" xs) -> gtAll pivot xs .=> gtAll pivot (quickSort xs)) [sorry]
    helper2 <- lemma "helper2" (\(Forall @"pivot" pivot) (Forall @"xs" xs) -> leAll pivot xs .=> leAll pivot (quickSort xs)) [sorry]

    sInductWith cvc5 "quickSortIsCorrect"
       (\(Forall @"xs" xs) -> let out = quickSort xs in nonDecreasing out .&& isPermutation xs out)
       (length @Integer) $
       \ih xs -> [] |-
           split xs
                 trivial
                 (\pivot as -> let (lo, hi) = untuple (partition pivot as)
                                   out      = quickSort lo ++ singleton pivot ++ quickSort hi
                            in nonDecreasing out .&& isPermutation (pivot .: as) out
                            ?? [ hprf $ ih                `at` Inst @"xs" lo
                               , hprf $ ih                `at` Inst @"xs" hi
                               , hprf $ partitionWorks    `at` (Inst @"pivot" pivot, Inst @"xs" as)
                               , hprf $ nonDecreasingJoin `at` (Inst @"lo" (quickSort lo), Inst @"pivot" pivot, Inst @"hi" (quickSort hi))
                               , hprf $ helper1           `at` (Inst @"pivot" pivot, Inst @"xs" lo)
                               , hprf $ helper2           `at` (Inst @"pivot" pivot, Inst @"xs" hi)
                               , hcmnt "jump"
                               ]
                            =: isPermutation (pivot .: as) out
                            =: qed)

-- nonDecreasing (quickSort lo)
-- isPermutation lo (quickSort lo)
-- nonDecreasing (quickSort hi)
-- isPermutation hi (quickSort hi)
-- gtAll pivot (fst (partition pivot as))
-- leAll pivot (snd (partition pivot as))
-- gtAll pivot (quickSort (fst (partition pivot as)))
-- leAll pivot (quickSort (snd (partition pivot as)))
