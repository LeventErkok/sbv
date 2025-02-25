-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.InsertionSort
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving insertion-sort correct.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.InsertionSort where

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

import Prelude hiding (null, length, head, tail)
import Data.SBV.List

-- | Insert an element into an already sorted list in the correct place.
insert :: SInteger -> SList Integer -> SList Integer
insert = smtFunction "insert" $ \e l -> ite (null l) (singleton e)
                                      $ let (x, xs) = uncons l
                                        in ite (e .<= x) (e .: x .: xs) (x .: insert e xs)

-- | Insertion sort, using 'insert' above to successively insert the elements.
insertionSort :: SList Integer -> SList Integer
insertionSort = smtFunction "insertionSort" $ \l -> ite (null l) nil
                                                  $ let (x, xs) = uncons l
                                                    in insert x (insertionSort xs)


-- | A predicate testing whether a given list is non-decreasing.
nonDecreasing :: SList Integer -> SBool
nonDecreasing = smtFunction "nonDecreasing" $ \l ->  null l .|| null (tail l)
                                                 .|| let (x, l') = uncons l
                                                         (y, _)  = uncons l'
                                                     in x .<= y .&& nonDecreasing l'

-- | Correctness of insertion-sort.
--
-- We have:
--
-- >>> correctness
correctness :: IO Proof
correctness = runKD $ do

    nonDecrTail <- lemma "nonDecTail"
                         (\(Forall @"x" x) (Forall @"xs" xs) -> nonDecreasing (x .: xs) .=> nonDecreasing xs)
                         []

    insertNonDecreasing <-
        induct "insertNonDecreasing"
               (\(Forall @"xs" xs) (Forall @"e" e) -> nonDecreasing xs .=> nonDecreasing (insert e xs)) $
               \ih x xs e -> [nonDecreasing (x .: xs)]
                          |- nonDecreasing (insert e (x .: xs))
                          ? "unfold insert"
                          =: nonDecreasing (ite (e .<= x) (e .: x .: xs) (x .: insert e xs))
                          ? "push nonDecreasing over the ite"
                          =: ite (e .<= x) (nonDecreasing (e .: x .: xs))
                                           (nonDecreasing (x .: insert e xs))
                          ? "unfold nonDecreasing, simplify"
                          =: ite (e .<= x)
                                 (nonDecreasing (x .: xs))
                                 (nonDecreasing (x .: insert e xs))
                          ?  nonDecreasing (x .: xs)
                          =: (e .> x .=> nonDecreasing (x .: insert e xs))
                          ? [ hyp (nonDecreasing (x .: xs))
                            , hprf (nonDecrTail `at` (Inst @"x" x, Inst @"xs" (insert e xs)))
                            , hprf ih
                            ]
                          =: sTrue
                          =: qed

    pure insertNonDecreasing
