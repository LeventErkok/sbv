-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.BinarySearch
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving binary search correct
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.BinarySearch where

import Prelude hiding (null, elem, notElem, tail, length, (!!))

import Data.SBV
import Data.SBV.List
import Data.SBV.Maybe
import Data.SBV.Tools.KnuckleDragger

-- * Binary search

-- | Encode binary search in a functional style. Note that since
-- functional lists in Haskell (or SMTLib) don't have constant time
-- access to arbitrary elements, this isn't really a fast implementation.
-- The idea here is to prove the algorithm correct, not it's complexity!
bsearch :: SInteger -> SList Integer -> SMaybe Integer
bsearch target elems = go target elems 0 (length elems - 1)
  where go = smtFunction "bsearch" $ \x xs low high ->
                ite (low .> high)
                    sNothing
                    (let mid  = low + (high - low) `sEDiv` 2
                         xmid = xs !! mid
                     in ite (xmid .== x)
                            (sJust mid)
                            (ite (xmid .< x)
                                 (go x xs (mid + 1) high)
                                 (go x xs low (mid - 1))))

-- * Correctness proof

-- | A predicate testing whether a given list is non-decreasing.
nonDecreasing :: SList Integer -> SBool
nonDecreasing = smtFunction "nonDecreasing" $ \l ->  null l .|| null (tail l)
                                                 .|| let (x, l') = uncons l
                                                         (y, _)  = uncons l'
                                                     in x .<= y .&& nonDecreasing l'

-- | Correctness of binary search.
--
-- We have:
--
-- >>> correctness
correctness :: IO Proof
correctness = runKD $ do

  -- Invariant: If @x@ is in @xs@ then, @x@ is between @xs[low .. high]@ at all times.

  -- First prove the result when the target is in the list
  bsearchP <- lemma "bsearchPresent"
                    (\(Forall @"x" x) (Forall @"xs" xs) ->
                         nonDecreasing xs .&& x `elem` xs .=> xs !! fromJust (bsearch x xs) .== x)
              [sorry]

  -- Now prove the result when the target is not in the list
  bsearchA <- lemma "bsearchAbsent"
                    (\(Forall @"x" x) (Forall @"xs" xs) -> x `notElem` xs .=> isNothing (bsearch x xs))
              [sorry]

  -- Prove the correctness using the helpers when target is in the list and otherwise:
  calc "bsearchCorrect"
        (\(Forall @"x" x) (Forall @"xs" xs) ->
             nonDecreasing xs .=> let res = bsearch x xs
                                  in ite (x `elem` xs)
                                         (xs !! fromJust res .== x)
                                         (isNothing res)) $
        \x xs -> [nonDecreasing xs]
              |- let res = bsearch x xs
                 in ite (x `elem` xs)
                        (xs !! fromJust res .== x)
                        (isNothing res)
              =: cases [ x `elem` xs    ==> xs !! fromJust (bsearch x xs) .== x
                                         ?? [hprf (bsearchP `at` (Inst @"x" x, Inst @"xs" xs)), hyp (nonDecreasing xs)]
                                         =: sTrue
                                         =: qed
                       , x `notElem` xs ==> isNothing (bsearch x xs)
                                         ?? [hprf (bsearchA `at` (Inst @"x" x, Inst @"xs" xs)), hyp (nonDecreasing xs)]
                                         =: sTrue
                                         =: qed
                       ]
