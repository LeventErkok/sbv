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

{-# LANGUAGE CPP                 #-}
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

#ifdef DOCTEST
-- $setup
-- >>> :set -XOverloadedLists
#endif

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
                                             $ let (h, t) = uncons xs
                                               in 0 `smax` (h `smax` (h + mssBegin t))

-- * Kadane's algorithm implementation

-- | Kadane algorithm: We call the helper with the values of maximum value ending
-- at the beginning and the list, and recurse.
--
-- >>> kadane [1, -2, 3, 4, -1, 2]  -- the segment: [3, 4, -1, 2]
-- 8 :: SInteger
-- >>> kadane [-2, -3, -1]          -- empty segment
-- 0 :: SInteger
-- >>> kadane [1, 2, 3]             -- the whole list
-- 6 :: SInteger
kadane :: SList Integer -> SInteger
kadane xs = kadaneHelper xs 0 0

-- | Helper for Kadane's algorithm. Along with the list, we keep track of the maximum-value
-- ending at the beginning of the list argument, and the maximum value sofar.
kadaneHelper :: SList Integer -> SInteger -> SInteger -> SInteger
kadaneHelper = smtFunction "kadaneHelper" $ \xs maxEndingHere maxSoFar ->
                    ite (null xs)
                        maxSoFar   -- end of the list, take the max-value calculated
                      $ let (h, t)           = uncons xs
                            newMaxEndingHere = 0 `smax` (h + maxEndingHere)     -- We can add head to the so far, or restart
                            newMaxSofar      = maxSoFar `smax` newMaxEndingHere -- Maximum of result so far, and the new
                        in kadaneHelper t newMaxEndingHere newMaxSofar

-- * Correctness proof
--
-- >>> runTPWith cvc5 correctness
correctness :: TP (Proof (Forall "xs" [Integer] -> SBool))
correctness =
   induct "correctness"
         (\(Forall xs) -> mss xs .== kadane xs) $
         \ih (x, xs) -> [] |- mss (x .: xs)
                           =: mssBegin (x .: xs) `smax` mss xs
                           ?? ih
                           =: mssBegin (x .: xs) `smax` kadane xs
                           =: (0 `smax` (x `smax` (x + mssBegin xs))) `smax` kadane xs
                           =: (0 `smax` (x `smax` (x + mssBegin xs))) `smax` kadaneHelper xs 0 0
                           ?? sorry
                           =: kadaneHelper xs (0 `smax` x) (0 `smax` x)
                           =: kadaneHelper xs (0 `smax` (x + 0)) (0 `smax` (0 `smax` (x + 0)))
                           =: kadaneHelper (x .: xs) 0 0
                           =: kadane (x .: xs)
                           =: qed
