-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.BinarySearch
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving binary search correct.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.BinarySearch where

import Prelude hiding (null, length, (!!), drop, take, tail, elem, notElem)

import Data.SBV
import Data.SBV.Maybe
import Data.SBV.TP

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
    \(Forall i) (Forall j) -> low .<= i .&& i .<= j .&& j .<= high .=> arr `readArray` i .<= arr `readArray` j

-- | A predicate testing whether an element is in the array within the given bounds
inArray :: Arr -> Idx -> SInteger -> SBool
inArray arr (low, high) elt = quantifiedBool $ \(Exists i) -> low .<= i .&& i .<= high .&& arr `readArray` i .== elt

-- | Correctness of binary search.
--
-- We have:
--
-- >>> correctness
-- Lemma: notInRange                                 Q.E.D.
-- Lemma: inRangeHigh                                Q.E.D.
-- Lemma: inRangeLow                                 Q.E.D.
-- Lemma: nonDecreasing                              Q.E.D.
-- Inductive lemma (strong): bsearchAbsent
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (unfold bsearch)                        Q.E.D.
--   Step: 2 (push isNothing down, simplify)         Q.E.D.
--   Step: 3 (2 way case split)
--     Step: 3.1                                     Q.E.D.
--     Step: 3.2.1                                   Q.E.D.
--     Step: 3.2.2                                   Q.E.D.
--     Step: 3.2.3                                   Q.E.D.
--     Step: 3.2.4                                   Q.E.D.
--     Step: 3.2.5 (simplify)                        Q.E.D.
--     Step: 3.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Inductive lemma (strong): bsearchPresent
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (unfold bsearch)                        Q.E.D.
--   Step: 2 (simplify)                              Q.E.D.
--   Step: 3 (3 way case split)
--     Step: 3.1                                     Q.E.D.
--     Step: 3.2                                     Q.E.D.
--     Step: 3.3.1                                   Q.E.D.
--     Step: 3.3.2 (3 way case split)
--       Step: 3.3.2.1                               Q.E.D.
--       Step: 3.3.2.2.1                             Q.E.D.
--       Step: 3.3.2.2.2                             Q.E.D.
--       Step: 3.3.2.3.1                             Q.E.D.
--       Step: 3.3.2.3.2                             Q.E.D.
--       Step: 3.3.2.Completeness                    Q.E.D.
--     Step: 3.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- Lemma: bsearchCorrect
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                   Q.E.D.
--     Step: 1.1.2                                   Q.E.D.
--     Step: 1.2.1                                   Q.E.D.
--     Step: 1.2.2                                   Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- [Proven] bsearchCorrect :: Ɐarr ∷ (ArrayModel Integer Integer) → Ɐlo ∷ Integer → Ɐhi ∷ Integer → Ɐx ∷ Integer → Bool
correctness :: IO (Proof (Forall "arr" (ArrayModel Integer Integer) -> Forall "lo" Integer -> Forall "hi" Integer -> Forall "x" Integer -> SBool))
correctness = runTPWith (tpRibbon 50 cvc5) $ do

  -- Helper: if a value is not in a range, then it isn't in any subrange of it:
  notInRange <- lemma "notInRange"
                           (\(Forall arr) (Forall lo) (Forall hi) (Forall md) (Forall x)
                               ->  sNot (inArray arr (lo, hi) x) .&& lo .<= md .&& md .<= hi
                               .=> sNot (inArray arr (lo, md) x) .&& sNot (inArray arr (md, hi) x))
                           []

  -- Helper: if a value is in a range of a nonDecreasing array, and if its value is larger than a given mid point, then it's in the higher part
  inRangeHigh <- lemma "inRangeHigh"
                       (\(Forall arr) (Forall lo) (Forall hi) (Forall md) (Forall x)
                           ->  nonDecreasing arr (lo, hi) .&& inArray arr (lo, hi) x .&& lo .<= md .&& md .<= hi .&& x .> arr `readArray` md
                           .=> inArray arr (md+1, hi) x)
                       []

  -- Helper: if a value is in a range of a nonDecreasing array, and if its value is lower than a given mid point, then it's in the lowr part
  inRangeLow  <- lemma "inRangeLow"
                       (\(Forall arr) (Forall lo) (Forall hi) (Forall md) (Forall x)
                           ->  nonDecreasing arr (lo, hi) .&& inArray arr (lo, hi) x .&& lo .<= md .&& md .<= hi .&& x .< arr `readArray` md
                           .=> inArray arr (lo, md-1) x)
                       []

  -- Helper: if an array is nonDecreasing, then its parts are also non-decreasing when cut in any middle point
  nonDecreasingInRange <- lemma "nonDecreasing"
                                (\(Forall arr) (Forall lo) (Forall hi) (Forall md)
                                    ->  nonDecreasing arr (lo, hi) .&& lo .<= md .&& md .<= hi
                                    .=> nonDecreasing arr (lo, md) .&& nonDecreasing arr (md, hi))
                                []

  -- Prove the case when the target is not in the array
  bsearchAbsent <- sInduct "bsearchAbsent"
        (\(Forall arr) (Forall lo) (Forall hi) (Forall x) ->
            nonDecreasing arr (lo, hi) .&& sNot (inArray arr (lo, hi) x) .=> isNothing (bsearch arr (lo, hi) x))
        (\_arr lo hi _x -> abs (hi - lo + 1), []) $
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
           =: cases [ lo .> hi  ==> trivial
                    , lo .<= hi ==> ite (xmid .== x)
                                        sFalse
                                        (ite (xmid .< x)
                                             (isNothing (bsearch arr (mid+1, hi)    x))
                                             (isNothing (bsearch arr (lo,    mid-1) x)))
                                 =: let inst1 l h m = (Inst @"arr" arr, Inst @"lo" l, Inst @"hi" h, Inst @"m" m, Inst @"x" x)
                                        inst2 l h m = (Inst @"arr" arr, Inst @"lo" l, Inst @"hi" h, Inst @"m" m             )
                                        inst3 l h   = (Inst @"arr" arr, Inst @"lo" l, Inst @"hi" h,              Inst @"x" x)
                                 in ite (xmid .< x)
                                        (isNothing (bsearch arr (mid+1, hi)    x))
                                        (isNothing (bsearch arr (lo,    mid-1) x))
                                 ?? notInRange           `at` inst1 lo      hi (mid+1)
                                 ?? nonDecreasingInRange `at` inst2 lo      hi (mid+1)
                                 ?? ih                   `at` inst3 (mid+1) hi
                                 =: ite (xmid .< x)
                                        sTrue
                                        (isNothing (bsearch arr (lo,    mid-1) x))
                                 ?? notInRange           `at` inst1 lo hi      (mid-1)
                                 ?? nonDecreasingInRange `at` inst2 lo hi      (mid-1)
                                 ?? ih                   `at` inst3 lo (mid-1)
                                 =: ite (xmid .< x) sTrue sTrue
                                 ?? "simplify"
                                 =: sTrue
                                 =: qed
                    ]

  -- Prove the case when the target is in the array
  bsearchPresent <- sInduct "bsearchPresent"
        (\(Forall arr) (Forall lo) (Forall hi) (Forall x) ->
            nonDecreasing arr (lo, hi) .&& inArray arr (lo, hi) x .=> arr `readArray` fromJust (bsearch arr (lo, hi) x) .== x)
        (\_arr lo hi _x -> abs (hi - lo + 1), []) $
        \ih arr lo hi x ->
             [nonDecreasing arr (lo, hi), inArray arr (lo, hi) x]
          |- x .== arr `readArray` fromJust (bsearch arr (lo, hi) x)
          ?? "unfold bsearch"
          =: let mid  = (lo + hi) `sEDiv` 2
                 xmid = arr `readArray` mid
          in x .== arr `readArray` fromJust (ite (lo .> hi)
                                                 sNothing
                                                 (ite (xmid .== x)
                                                      (sJust mid)
                                                      (ite (xmid .< x)
                                                           (bsearch arr (mid+1, hi)    x)
                                                           (bsearch arr (lo,    mid-1) x))))
          ?? "simplify"
          =: ite (lo .> hi)
                 (x .== arr `readArray` fromJust sNothing)
                 (ite (xmid .== x)
                      (x .== arr `readArray` mid)
                      (ite (xmid .< x)
                           (x .== arr `readArray` fromJust (bsearch arr (mid+1, hi)    x))
                           (x .== arr `readArray` fromJust (bsearch arr (lo,    mid-1) x))))
          =: cases [ lo .>  hi ==> trivial
                   , lo .== hi ==> trivial
                   , lo .<  hi ==> ite (xmid .== x)
                                       (x .== arr `readArray` mid)
                                       (ite (xmid .< x)
                                            (x .== arr `readArray` fromJust (bsearch arr (mid+1, hi)    x))
                                            (x .== arr `readArray` fromJust (bsearch arr (lo,    mid-1) x)))
                                =: let inst1 l h m = (Inst @"arr" arr, Inst @"lo" l, Inst @"hi" h, Inst @"m" m, Inst @"x" x)
                                       inst2 l h m = (Inst @"arr" arr, Inst @"lo" l, Inst @"hi" h, Inst @"m" m             )
                                       inst3 l h   = (Inst @"arr" arr, Inst @"lo" l, Inst @"hi" h,              Inst @"x" x)
                                in cases [ xmid .== x ==> trivial
                                         , xmid .< x  ==> x .== arr `readArray` fromJust (bsearch arr (mid+1, hi)    x)
                                                       ?? inRangeHigh          `at` inst1 lo      hi mid
                                                       ?? nonDecreasingInRange `at` inst2 lo      hi (mid+1)
                                                       ?? ih                   `at` inst3 (mid+1) hi
                                                       =: sTrue
                                                       =: qed
                                         , xmid .> x  ==> x .== arr `readArray` fromJust (bsearch arr (lo, mid-1) x)
                                                       ?? inRangeLow           `at` inst1 lo hi      mid
                                                       ?? nonDecreasingInRange `at` inst2 lo hi      (mid-1)
                                                       ?? ih                   `at` inst3 lo (mid-1)
                                                       =: sTrue
                                                       =: qed
                                         ]
                   ]

  calc "bsearchCorrect"
        (\(Forall arr) (Forall lo) (Forall hi) (Forall x) ->
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
                                   ?? bsearchPresent `at` (Inst @"arr" arr, Inst @"lo" lo, Inst @"hi" hi, Inst @"x" x)
                                   =: sTrue
                                   =: qed
                              , sNot (inArray arr (lo, hi) x)
                                  ==> isNothing (bsearch arr (lo, hi) x)
                                   ?? bsearchAbsent `at` (Inst @"arr" arr, Inst @"lo" lo, Inst @"hi" hi, Inst @"x" x)
                                   =: sTrue
                                   =: qed
                              ]

{- HLint ignore module "Reduce duplication" -}
