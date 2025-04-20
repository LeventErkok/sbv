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

import Prelude hiding (null, length, (!!), drop, take, tail, elem, notElem)

import Data.SBV
import Data.SBV.List
import Data.SBV.Maybe
import Data.SBV.Tools.KnuckleDragger

import qualified Data.SBV.Maybe as SM

-- * Binary search

-- | Encode binary search in a functional style. Note that since
-- functional lists in Haskell (or SMTLib) don't have constant time
-- access to arbitrary elements, this isn't really a fast implementation.
-- The idea here is to prove the algorithm correct, not its complexity!
bsearch :: SList Integer -> SInteger -> SMaybe Integer
bsearch = smtFunction "bsearch" $ \xs x ->
    ite (null xs)
        sNothing
        (let mid  = (length xs - 1) `sEDiv` 2
             xmid = xs !! mid
             mid1 = mid + 1
         in ite (xmid .== x)
                (sJust mid)
                (ite (xmid .< x)
                     (SM.map (+ mid1) (bsearch (drop mid1 xs) x))
                     (                 bsearch (take mid  xs) x)))


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

  -- Prove the case when the target is in the list
  bsearchPresent <- lemma "bsearchPresent"
        (\(Forall @"xs" xs) (Forall @"x" x) ->
            nonDecreasing xs .&& x `elem` xs .=> xs !! fromJust (bsearch xs x) .== x)
        [sorry]

  -- Prove the case when the target is not in the list
  bsearchAbsent <- lemma "bsearchAbsent"
        (\(Forall @"xs" xs) (Forall @"x" x) ->
            nonDecreasing xs .&& x `notElem` xs .=> isNothing (bsearch xs x))
        [sorry]

  -- Combine the above two results for the final theorem:
  calc "bsearchCorrect"
        (\(Forall @"xs" xs) (Forall @"x" x) ->
            nonDecreasing xs .=> let res = bsearch xs x
                                 in ite (x `elem` xs)
                                        (xs !! fromJust res .== x)
                                        (isNothing res)) $
        \xs x -> [nonDecreasing xs]
              |- let res = bsearch xs x
                 in ite (x `elem` xs)
                        (xs !! fromJust res .== x)
                        (isNothing res)
              =: cases [ x `elem` xs    ==> xs !! fromJust (bsearch xs x) .== x
                                         ?? [ hyp  (nonDecreasing xs)
                                            , hprf (bsearchPresent `at` (Inst @"xs" xs, Inst @"x" x))
                                            ]
                                         =: sTrue
                                         =: qed
                       , x `notElem` xs ==> isNothing (bsearch xs x)
                                         ?? [ hyp  (nonDecreasing xs)
                                            , hprf (bsearchAbsent `at` (Inst @"xs" xs, Inst @"x" x))
                                            ]
                                         =: sTrue
                                         =: qed
                       ]
