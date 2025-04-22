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
import Data.SBV.Maybe
import Data.SBV.Tools.KnuckleDragger

-- * Binary search

-- | We will work with arrays containing integers, indexed by integers. Note that since SMTLib arrays
-- are indexed by their entire domain, we explicitly take a lower/upper bounds as parameters, which fits well
-- with the binary search algorithm.
type Arr = SArray Integer Integer

-- | Bounds: This is the focus into the array; both indexes are inclusive.
type Idx = (SInteger, SInteger)

-- | Encode binary search in a functional style.
bsearch :: Arr -> Idx -> SInteger -> SMaybe Integer
bsearch arr (low, high) = f arr low high
  where f = smtFunction "bsearch" $ \a lo hi x ->
               let mid  = (lo + hi) `sEDiv` 2
                   xmid = a `readArray` mid
               in ite (lo .> hi)
                      sNothing
                      (ite (xmid .== x)
                           (sJust mid)
                           (ite (xmid .< x)
                                (bsearch a (mid+1, hi)    x)
                                (bsearch a (lo,    mid-1) x)))

-- * Correctness proof

-- | A predicate testing whether a given array is non-decreasing in the given range
nonDecreasing :: Arr -> Idx -> SBool
nonDecreasing arr (low, high) = quantifiedBool $
    \(Forall @"i" i) (Forall @"j" j) -> low .<= i .&& i .<= j .&& j .<= high .=> arr `readArray` i .<= arr `readArray` j

-- | A predicate testing whether an element is in the array within the given bounds
inArray :: Arr -> Idx -> SInteger -> SBool
inArray arr (low, high) elt = quantifiedBool $ \(Exists @"i" i) -> low .<= i .&& i .<= high .&& arr `readArray` i .== elt

-- | Correctness of binary search.
--
-- We have:
--
-- >>> correctness
correctness :: IO Proof
correctness = runKD $ do

  -- Prove the case when the target is not in the array
  bsearchAbsent <- lemma "bsearchAbsent"
        (\(Forall @"arr" arr) (Forall @"lo" lo) (Forall @"hi" hi) (Forall @"x" x) ->
            nonDecreasing arr (lo, hi) .&& sNot (inArray arr (lo, hi) x) .=> isNothing (bsearch arr (lo, hi) x))
        [sorry]

  -- Prove the case when the target is in the array
  bsearchPresent <- lemma "bsearchPresent"
        (\(Forall @"arr" arr) (Forall @"lo" lo) (Forall @"hi" hi) (Forall @"x" x) ->
            nonDecreasing arr (lo, hi) .&& inArray arr (lo, hi) x .=> arr `readArray` fromJust (bsearch arr (lo, hi) x) .== x)
        [sorry]

  calc "bsearchCorrect"
        (\(Forall @"arr" arr) (Forall @"lo" lo) (Forall @"hi" hi) (Forall @"x" x) ->
            nonDecreasing arr (lo, hi) .=> let res = bsearch arr (lo, hi) x
                                           in ite (inArray arr (lo, hi) x)
                                                  (arr `readArray` fromJust res .== x)
                                                  (isNothing res)) $
        \arr lo hi x -> [nonDecreasing arr (lo, hi)]
                     |- let res = bsearch arr (lo, hi) x
                        in ite (inArray arr (lo, hi) x)
                               (arr `readArray` fromJust res .== x)
                               (isNothing res)
                     =: cases [ inArray arr (lo, hi) x
                                  ==> arr `readArray` fromJust (bsearch arr (lo, hi) x) .== x
                                   ?? [ hyp  (nonDecreasing arr (lo, hi))
                                      , hprf (bsearchPresent `at` (Inst @"arr" arr, Inst @"lo" lo, Inst @"hi" hi, Inst @"x" x))
                                      ]
                                   =: sTrue
                                   =: qed
                              , sNot (inArray arr (lo, hi) x)
                                  ==> isNothing (bsearch arr (lo, hi) x)
                                   ?? [ hyp  (nonDecreasing arr (lo, hi))
                                      , hprf (bsearchAbsent `at` (Inst @"arr" arr, Inst @"lo" lo, Inst @"hi" hi, Inst @"x" x))
                                      ]
                                   =: sTrue
                                   =: qed
                              ]
                     =: qed

{-
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
  lemma "bsearchCorrect"
        (\(Forall @"arr" arr) (Forall @"low" low) (Forall @"high" high) (Forall @"x" x) ->
            nonDecreasing arr 0  .=> let res = bsearch xs x
                                 in ite (x `elem` xs)
                                        (xs !! fromJust res .== x)
                                        (isNothing res)) $
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

  -- helper: if an element is present and is less than another element, it must be in the prefix
  presentInPrefix <- induct "presentInPrefix"
      (\(Forall @"xs" xs) (Forall @"n" n) (Forall @"e" e) ->
          n .>= 0 .&& n .< length xs .&& nonDecreasing xs .&& e `elem` xs .&& e .< xs !! n .=> e `elem` take n xs) $
      \ih x xs n e -> [ n .>= 0
                      , n .< length (x .: xs)
                      , nonDecreasing (x .: xs)
                      , e `elem` (x .: xs)
                      , e .< (x .: xs) !! n
                      ]
                   |- e `elem` take n (x .: xs)
                   =: cases [ n .<= 0 ==> trivial
                            , n .>  0 ==> e `elem` (x .: take (n-1) xs)
                                       =: cases [ e .== x ==> trivial
                                                , e ./= x ==> e `elem` take (n-1) xs
                                                           ?? [ ih                  `at` (Inst @"n" (n-1), Inst @"e" e)
                                                              , nonDecreasingSuffix `at` (Inst @"xs" xs, Inst @"n" (1::SInteger))
                                                              ]
                                                           =: sTrue
                                                           =: qed
                                                ]
                            ]

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
  bsearchPresent <- sInductWith cvc5 "bsearchPresent"
        (\(Forall @"xs" xs) (Forall @"x" x) ->
            nonDecreasing xs .&& x `elem` xs .=> xs !! fromJust (bsearch xs x) .== x) $
        \ih xs x -> [nonDecreasing xs, x `elem` xs]
                 |- xs !! fromJust (bsearch xs x) .== x
                 ?? "expand bsearch and push fromJust down"
                 =: let mid  = (length xs - 1) `sEDiv` 2
                        xmid = xs !! mid
                        mid1 = mid + 1
                 in ite (null xs)
                        (x .== xs !! fromJust (bsearch xs x))
                        (ite (xmid .== x)
                             sTrue
                             (ite (xmid .< x)
                                  (x .== xs !! fromJust (SM.map (+ mid1) (bsearch (drop mid1 xs) x)))
                                  (x .== xs !! fromJust (                 bsearch (take mid  xs) x))))
                 ?? x `elem` xs
                 =: ite (xmid .== x)
                        sTrue
                        (ite (xmid .< x)
                             (x .== xs !! fromJust (SM.map (+ mid1) (bsearch (drop mid1 xs) x)))
                             (x .== xs !! fromJust (                 bsearch (take mid  xs) x)))
                 =: cases [ xmid .== x ==> trivial
                          , xmid .> x  ==> x .== xs !! fromJust (bsearch (take mid xs) x)
                                        ?? [ hprf (ih                  `at` (Inst @"xs" (take mid xs), Inst @"x" x))
                                           , hprf (nonDecreasingPrefix `at` (Inst @"n" mid, Inst @"xs" xs))
                                           , hprf (presentInPrefix     `at` (Inst @"n" mid, Inst @"x" x, Inst @"xs" xs))
                                           ]
                                        =: sTrue
                                        =: qed
                          , xmid .< x  ==> x .== xs !! fromJust (SM.map (+ mid1) (bsearch (drop mid1 xs) x))
                                        ?? sorry
                                        =: sTrue
                                        =: qed
                          ]

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
-}
