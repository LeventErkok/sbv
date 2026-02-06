-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Kadane
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving the correctness of Kadane's algorithm for computing the maximum
-- sum of any contiguous subarray (maximum segment sum problem).
--
-- Kadane's algorithm is a classic dynamic programming algorithm that solves
-- the maximum segment sum problem in O(n) time. Given a list of integers,
-- it finds the maximum sum of any contiguous subarray, where the empty
-- subarray has sum 0.
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
--
-- For example:
--   mss [1, -2, 3, 4, -1, 2] = 8  (the segment [3, 4, -1, 2])
--   mss [-2, -3, -1]         = 0  (the empty segment)
--   mss [1, 2, 3]            = 6  (the whole list)

-- | Maximum of two integers.
maxOf :: SInteger -> SInteger -> SInteger
maxOf x y = ite (x .>= y) x y

-- | Maximum segment sum (specification). This is what we want to compute.
-- We define it as the maximum sum over all segments, including the empty segment.
mss :: SList Integer -> SInteger
mss = smtFunction "mss" $ \xs ->
    ite (null xs)
        0  -- empty list: best segment is empty with sum 0
        (let tailMss = mss (tail xs)
             -- Best segment either doesn't include the head, or starts at the head
             maxStartingHere = maxSumStartingAt xs
         in maxOf tailMss maxStartingHere)

-- | Maximum sum of segments starting at the beginning of the list.
-- This is 0 if the empty segment is best, or positive if a non-empty prefix is best.
maxSumStartingAt :: SList Integer -> SInteger
maxSumStartingAt = smtFunction "maxSumStartingAt" $ \xs ->
    ite (null xs)
        0
        (let h = head xs
             t = tail xs
             -- Either take just the head (if positive), or extend with tail
             restSum = maxSumStartingAt t
         in maxOf 0 (maxOf h (h + restSum)))

-- * Kadane's algorithm implementation

-- | Helper: maximum sum ending at the end of the list.
-- This represents the maximum sum of any segment that ends at the last position.
maxEndingAt :: SList Integer -> SInteger
maxEndingAt = smtFunction "maxEndingAt" $ \xs ->
    ite (null xs)
        0
        (maxOf 0 (head xs + maxEndingAt (tail xs)))

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
         in maxOf tailResult endingHere)

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
                             =: maxOf 0 (x + maxEndingAt xs) .<= mss xs
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
                             =: maxOf (kadane xs) (maxEndingAt (x .: xs))
                             ?? ih
                             =: maxOf (mss xs) (maxEndingAt (x .: xs))
                             ?? leqLemma
                             ?? mssNN
                             ?? nonNeg
                             =: mss (x .: xs)
                             =: qed

{- HLint ignore module "Eta reduce" -}
