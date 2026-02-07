-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Kadane
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving the correctness of Kadane's algorithm for computing the maximum
-- sum of any contiguous list (maximum segment sum problem).
--
-- Kadane's algorithm is a classic dynamic programming algorithm that solves
-- the maximum segment sum problem in O(n) time. Given a list of integers,
-- it finds the maximum sum of any contiguous list, where the empty
-- list has sum 0.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Kadane where

import Prelude hiding (length, maximum, null, head, tail, (++))

import Data.SBV
import Data.SBV.List
import Data.SBV.TP

-- * Problem specification

-- | The maximum segment sum problem: Find the maximum sum of any contiguous
-- subarray. We include the empty subarray (with sum 0) as a valid segment.
-- This is the obvious definition: Empty list maps to 0. Otherwise, we take the
-- value of the segment starting at the current position, and take the maximum
-- of that value with the recursive result of the tail. This is obviously
-- correct, but has the runtime of O(n^2).
--
-- We have:
--
-- >>> mss [1, -2, 3, 4, -1, 2]  -- the segment: [3, 4, -1, 2]
-- 8 :: SInteger
-- >>> mss [-2, -3, -1]          -- empty segment
-- 0 :: SInteger
-- >>> mss [1, 2, 3]             -- the whole list
-- 6 :: SInteger
mss :: SList Integer -> SInteger
mss = smtFunction "mss" $ \xs -> ite (null xs) 0 (mssBegin xs `smax` mss (tail xs))

-- | Maximum sum of segments starting at the beginning of the given list.
-- This is 0 if the empty segment is best, or positive if a non-empty prefix exists.
--
-- We have:
--
-- >>> mssBegin [1, -2, 3, 4, -1, 2]  -- the segment: [1, -2, 3, 4, -1, 2]
-- 7 :: SInteger
-- >>> mssBegin [-2, -3, -1]          -- empty segment
-- 0 :: SInteger
-- >>> mssBegin [1, 2, 3]             -- the whole list
-- 6 :: SInteger
mssBegin :: SList Integer -> SInteger
mssBegin = smtFunction "mssBegin" $ \xs -> ite (null xs) 0
                                               (let (h, t) = uncons xs
                                                in 0 `smax` (h `smax` (h + mssBegin t)))

-- * Kadane's algorithm implementation

-- | Helper: maximum sum ending at the end of the list.
-- This represents the maximum sum of any segment that ends at the last position.
maxEndingAt :: SList Integer -> SInteger
maxEndingAt = smtFunction "maxEndingAt" $ \xs ->
    ite (null xs)
        0
        (0 `smax` (head xs + maxEndingAt (tail xs)))

-- | Kadane's algorithm: compute maximum segment sum recursively.
-- At each step, the result is the maximum of:
--   1. The best from the tail (doesn't include current element)
--   2. The best ending at current position (maxEndingAt)
kadane :: SList Integer -> SInteger
kadane = smtFunction "kadane" $ \xs ->
    ite (null xs)
        0
        (let tailResult = kadane (tail xs)
             endingHere = maxEndingAt xs
         in tailResult `smax` endingHere)

-- * Helper lemmas

-- | The maximum sum ending at any position is always non-negative.
maxEndingAtNonNeg :: TP (Proof (Forall "xs" [Integer] -> SBool))
maxEndingAtNonNeg = lemmaWith cvc5 "maxEndingAtNonNeg" (\(Forall xs) -> maxEndingAt xs .>= 0) []

-- | The maximum segment sum is always non-negative (empty segment has sum 0).
mssNonNeg :: TP (Proof (Forall "xs" [Integer] -> SBool))
mssNonNeg = lemmaWith cvc5 "mssNonNeg" (\(Forall xs) -> mss xs .>= 0) []

-- | Relationship between maxEndingAt and mss:
-- The max ending at the end is at most the overall max.
maxEndingAtLeqMss :: TP (Proof (Forall "xs" [Integer] -> SBool))
maxEndingAtLeqMss =
    induct "maxEndingAtLeqMss"
           (\(Forall xs) -> maxEndingAt xs .<= mss xs) $
           \ih (x, xs) -> [] |- maxEndingAt (x .: xs) .<= mss (x .: xs)
                             =: 0 `smax` (x + maxEndingAt xs) .<= mss xs
                             ?? ih
                             =: sTrue
                             =: qed

-- * Main correctness theorem

-- | Correctness of Kadane's algorithm: it computes the maximum segment sum.
--
-- We prove that for all lists xs, kadane xs = mss xs.
--
-- The proof proceeds by induction on the list structure, using the key
-- lemmas about maxEndingAt.
--
-- We have:
--
-- >>> correctness
-- Inductive lemma: maxEndingAtNonNeg
-- ...
correctness :: IO (Proof (Forall "xs" [Integer] -> SBool))
correctness = runTP $ do

    -- First prove helper lemmas
    nonNeg   <- maxEndingAtNonNeg
    mssNN    <- mssNonNeg
    leqLemma <- maxEndingAtLeqMss

    -- Main correctness proof by induction
    induct "kadaneCorrect"
           (\(Forall xs) -> kadane xs .== mss xs) $
           \ih (x, xs) -> [] |- kadane (x .: xs)
                             =: kadane xs `smax` maxEndingAt (x .: xs)
                             ?? ih
                             =: mss xs `smax` maxEndingAt (x .: xs)
                             ?? leqLemma
                             ?? mssNN
                             ?? nonNeg
                             =: mss (x .: xs)
                             =: qed

{- HLint ignore module "Eta reduce" -}
