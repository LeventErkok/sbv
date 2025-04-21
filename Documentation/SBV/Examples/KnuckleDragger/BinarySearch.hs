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
correctness = runKDWith z3{kdOptions = (kdOptions z3) { ribbonLength = 50 }} $ do

  -- helper: if an element is not in a list, then it isn't an element of any of its suffixes either
  notElemSuffix <- lemma "notElemSuffix"
        (\(Forall @"n" n) (Forall @"x" (x :: SInteger)) (Forall @"xs" xs) -> x `notElem` xs .=> x `notElem` drop n xs)
        []

  -- helper: if an element is not in a list, then it isn't an element of any of its prefixes either
  notElemPrefix <- lemma "notElemPrefix"
        (\(Forall @"n" n) (Forall @"x" (x :: SInteger)) (Forall @"xs" xs) -> x `notElem` xs .=> x `notElem` take n xs)
        []

  -- helper: if a list is non-decreasing, so is any suffix of it
  nonDecreasingSuffix <- inductWith cvc5 "nonDecreasingSuffix"
        (\(Forall @"xs" xs) (Forall @"n" n) -> nonDecreasing xs .=> nonDecreasing (drop n xs)) $
        \ih x xs n -> [nonDecreasing (x .: xs)]
                   |- nonDecreasing (drop n (x .: xs))
                   =: cases [ n .<= 0 ==> trivial
                            , n .> 0  ==> nonDecreasing (drop (n-1) xs)
                                       ?? [ hprf (ih `at` Inst @"n" (n-1))
                                          , hyp  (nonDecreasing xs)
                                          ]
                                       =: sTrue
                                       =: qed
                            ]

  -- helper: if a list is non-decreasing, so is any prefix of it
  nonDecreasingPrefix <- inductWith cvc5 "nonDecreasingPrefix"
        (\(Forall @"n" n) (Forall @"xs" xs) -> nonDecreasing xs .=> nonDecreasing (take n xs)) $
        \ih n xs -> [nonDecreasing xs]
                 |- nonDecreasing (take (n+1) xs)
                 =: split xs
                          trivial
                          (\a as -> nonDecreasing (a .: take n as)
                                 =: cases [ n .<= 0 ==> trivial
                                          , n .> 0  ==> split as
                                                              trivial
                                                              (\b bs -> nonDecreasing (a .: b .: take (n-1) bs)
                                                                     ?? [ hprf ih
                                                                        , hyp (nonDecreasing xs)
                                                                        ]
                                                                     =: sTrue
                                                                     =: qed)
                                          ])

  -- Prove the case when the target is not in the list
  bsearchAbsent <- sInductWith cvc5 "bsearchAbsent"
        (\(Forall @"xs" xs) (Forall @"x" x) ->
            nonDecreasing xs .&& x `notElem` xs .=> isNothing (bsearch xs x)) $
        \ih xs x -> [nonDecreasing xs, x `notElem` xs]
                 |- isNothing (bsearch xs x)
                 ?? "expand bsearch and push isNothing down"
                 =: let mid  = (length xs - 1) `sEDiv` 2
                        xmid = xs !! mid
                        mid1 = mid + 1
                 in ite (null xs)
                        sTrue
                        (ite (xmid .== x)
                             sFalse
                             (ite (xmid .< x)
                                  (isNothing (SM.map (+ mid1) (bsearch (drop mid1 xs) x)))
                                  (isNothing (                 bsearch (take mid  xs) x))))
                 ?? [ hprf (ih                  `at` (Inst @"xs" (drop mid1 xs), Inst @"x" x))
                    , hprf (notElemSuffix       `at` (Inst @"n" mid1, Inst @"x" x, Inst @"xs" xs))
                    , hprf (nonDecreasingSuffix `at` (Inst @"xs" xs, Inst @"n" mid1))
                    , hyp  (nonDecreasing xs)
                    , hyp  (x `notElem` xs)
                    ]
                 =: ite (null xs)
                        sTrue
                        (ite (xmid .== x)
                             sFalse
                             (ite (xmid .< x)
                                  (isNothing (SM.map (+ mid1) sNothing))
                                  (isNothing (bsearch (take mid xs) x))))
                 ?? [ hprf (ih                  `at` (Inst @"xs" (take mid xs), Inst @"x" x))
                    , hprf (notElemPrefix       `at` (Inst @"n" mid, Inst @"x" x, Inst @"xs" xs))
                    , hprf (nonDecreasingPrefix `at` (Inst @"n" mid,              Inst @"xs" xs))
                    , hyp  (nonDecreasing xs)
                    , hyp  (x `notElem` xs)
                    ]
                 =: ite (null xs)
                        sTrue
                        (ite (xmid .== x)
                             sFalse
                             (ite (xmid .< x)
                                  (isNothing (SM.map (+ mid1) sNothing))
                                  (isNothing (sNothing :: SMaybe Integer))))
                 ?? "simplify"
                 =: null xs .|| xmid ./== x
                 =: qed

  -- Prove the case when the target is in the list
  bsearchPresent <- lemma "bsearchPresent"
        (\(Forall @"xs" xs) (Forall @"x" x) ->
            nonDecreasing xs .&& x `elem` xs .=> xs !! fromJust (bsearch xs x) .== x)
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
