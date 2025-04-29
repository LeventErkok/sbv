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
bsearch array (low, high) = f array low high
  where f = smtFunction "bsearch" $ \arr lo hi x ->
               let mid  = (lo + hi) `sEDiv` 2
                   xmid = arr `readArray` mid
               in ite (lo .> hi)
                      sNothing
                      (ite (xmid .== x)
                           (sJust mid)
                           (ite (xmid .< x)
                                (bsearch arr (mid+1, hi)    x)
                                (bsearch arr (lo,    mid-1) x)))

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
correctness = runKDWith z3{kdOptions = (kdOptions z3) { ribbonLength = 50 }} $ do

  -- Helper: if a value is not in a range, then it isn't in any subrange of it:
  notInRange <- lemma "notInRange"
                      (\(Forall @"arr" arr) (Forall @"lo" lo) (Forall @"hi" hi) (Forall @"m" md) (Forall @"x" x)
                          ->  sNot (inArray arr (lo, hi) x) .&& lo .<= md .&& md .<= hi
                          .=> sNot (inArray arr (lo, md) x) .&& sNot (inArray arr (md, hi) x))
                      []

  -- Helper: if an array is nonDecreasing, then its parts are also non-decreasing when cut in any middle point
  nonDecreasingInRange <- lemma "nonDecreasing"
                                (\(Forall @"arr" arr) (Forall @"lo" lo) (Forall @"hi" hi) (Forall @"m" md)
                                    ->  nonDecreasing arr (lo, hi) .&& lo .<= md .&& md .<= hi
                                    .=> nonDecreasing arr (lo, md) .&& nonDecreasing arr (md, hi))
                                []

  -- Prove the case when the target is not in the array
  bsearchAbsent <- sInduct "bsearchAbsent"
        (\(Forall @"arr" arr) (Forall @"lo" lo) (Forall @"hi" hi) (Forall @"x" x) ->
            nonDecreasing arr (lo, hi) .&& sNot (inArray arr (lo, hi) x) .=> isNothing (bsearch arr (lo, hi) x))
        (\(_arr :: Arr) (lo :: SInteger) (hi :: SInteger) (_x :: SInteger) -> abs (hi - lo + 1)) $
        \ih arr lo hi x ->
              [nonDecreasing arr (lo, hi), sNot (inArray arr (lo, hi) x)]
           |- isNothing (bsearch arr (lo, hi) x)
           ?? "unfold bsearch"
           =: let mid  = (lo + hi) `sEDiv` 2
                  xmid = arr `readArray` mid
           in isNothing (ite (lo .> hi)
                             sNothing
                             (ite (xmid .== x)
                                  (sJust mid)
                                  (ite (xmid .< x)
                                       (bsearch arr (mid+1, hi)    x)
                                       (bsearch arr (lo,    mid-1) x))))
           ?? "push isNothing down, simplify"
           =: ite (lo .> hi)
                  sTrue
                  (ite (xmid .== x)
                       sFalse
                       (ite (xmid .< x)
                            (isNothing (bsearch arr (mid+1, hi)    x))
                            (isNothing (bsearch arr (lo,    mid-1) x))))
           =: cases [ lo .> hi  ==> qed
                    , lo .<= hi ==> ite (xmid .== x)
                                        sFalse
                                        (ite (xmid .< x)
                                             (isNothing (bsearch arr (mid+1, hi)    x))
                                             (isNothing (bsearch arr (lo,    mid-1) x)))
                                 ?? sNot (inArray arr (lo, hi) x)
                                 =: ite (xmid .< x)
                                        (isNothing (bsearch arr (mid+1, hi)    x))
                                        (isNothing (bsearch arr (lo,    mid-1) x))
                                 ?? [ hprf $ notInRange           `at` (Inst @"arr" arr, Inst @"lo" lo,      Inst @"hi" hi, Inst @"m" (mid+1), Inst @"x" x)
                                    , hprf $ nonDecreasingInRange `at` (Inst @"arr" arr, Inst @"lo" lo,      Inst @"hi" hi, Inst @"m" (mid+1))
                                    , hprf $ ih                   `at` (Inst @"arr" arr, Inst @"lo" (mid+1), Inst @"hi" hi,                    Inst @"x" x)
                                    , hasm $ sNot (inArray arr (lo, hi) x)
                                    , hasm $ nonDecreasing arr (lo, hi)
                                    ]
                                 =: ite (xmid .< x)
                                        sTrue
                                        (isNothing (bsearch arr (lo,    mid-1) x))
                                 ?? [ hprf $ notInRange           `at` (Inst @"arr" arr, Inst @"lo" lo, Inst @"hi" hi,      Inst @"m" (mid-1), Inst @"x" x)
                                    , hprf $ nonDecreasingInRange `at` (Inst @"arr" arr, Inst @"lo" lo, Inst @"hi" hi,      Inst @"m" (mid-1))
                                    , hprf $ ih                   `at` (Inst @"arr" arr, Inst @"lo" lo, Inst @"hi" (mid-1),                    Inst @"x" x)
                                    , hasm $ sNot (inArray arr (lo, hi) x)
                                    , hasm $ nonDecreasing arr (lo, hi)
                                    ]
                                 =: ite (xmid .< x)
                                        sTrue
                                        sTrue
                                 ?? "simplify"
                                 =: sTrue
                                 =: qed
                    ]

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
                                   ?? [ hasm (nonDecreasing arr (lo, hi))
                                      , hprf (bsearchPresent `at` (Inst @"arr" arr, Inst @"lo" lo, Inst @"hi" hi, Inst @"x" x))
                                      ]
                                   =: sTrue
                                   =: qed
                              , sNot (inArray arr (lo, hi) x)
                                  ==> isNothing (bsearch arr (lo, hi) x)
                                   ?? [ hasm (nonDecreasing arr (lo, hi))
                                      , hprf (bsearchAbsent `at` (Inst @"arr" arr, Inst @"lo" lo, Inst @"hi" hi, Inst @"x" x))
                                      ]
                                   =: sTrue
                                   =: qed
                              ]
