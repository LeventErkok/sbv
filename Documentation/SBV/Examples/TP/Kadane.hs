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
-- >>> import Data.SBV
-- >>> import Data.SBV.TP
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
-- The key insight is that we need a generalized invariant that characterizes
-- @kadaneHelper@ for arbitrary accumulator values, not just the initial @(0, 0)@.
--
-- The invariant states: for @kadaneHelper xs meh msf@ where:
--
--   * @meh@ (max-ending-here) is the maximum sum of a segment ending at the boundary
--   * @msf@ (max-so-far) is the best segment sum seen in the already-processed prefix
--   * Preconditions: @meh >= 0@ and @msf >= meh@
--
-- @
--   kadaneHelper xs meh msf == msf `smax` mss xs `smax` (meh + mssBegin xs)
-- @
--
-- This captures that the result is the maximum of:
--
--   * @msf@ - the best segment entirely in the already-processed prefix
--   * @mss xs@ - the best segment entirely in the remaining suffix
--   * @meh + mssBegin xs@ - the best segment crossing the boundary
--
-- >>> runTPWith cvc5 correctness
-- Inductive lemma (strong): kadaneHelperInvariant
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way full case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.2.4                         Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: correctness
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] correctness :: Ɐxs ∷ [Integer] → Bool
correctness :: TP (Proof (Forall "xs" [Integer] -> SBool))
correctness = do

  -- First, prove the generalized invariant using strong induction on list length.
  -- This is the heart of the proof: it relates kadaneHelper with arbitrary
  -- accumulators to the specification functions mss and mssBegin.
  invariant <- sInduct "kadaneHelperInvariant"
      (\(Forall xs) (Forall meh) (Forall msf) ->
         (meh .>= 0 .&& msf .>= meh) .=> kadaneHelper xs meh msf .== (msf `smax` mss xs `smax` (meh + mssBegin xs)))
      (\xs _ _ -> length xs, []) $
      \ih xs meh msf ->
        [meh .>= 0, msf .>= meh] |- split xs
                                          trivial   -- Base case: empty list, solver handles this by itself
                                          (\a as -> -- Inductive case: non-empty list (a : as)
                                             let newMeh = 0 `smax` (a + meh)
                                                 newMsf = msf `smax` newMeh
                                             in kadaneHelper (a .: as) meh msf
                                             =: kadaneHelper as newMeh newMsf
                                             -- Apply IH: need newMeh >= 0 and newMsf >= newMeh (both hold by construction)
                                             ?? ih `at` (Inst @"xs" as, Inst @"meh" newMeh, Inst @"msf" newMsf)
                                             =: newMsf `smax` mss as `smax` (newMeh + mssBegin as)
                                             -- Expand definitions and simplify
                                             =: (msf `smax` (0 `smax` (a + meh))) `smax` mss as `smax` ((0 `smax` (a + meh)) + mssBegin as)
                                             -- The key algebraic step: this equals the RHS for (a:as)
                                             -- mss (a:as) = mssBegin (a:as) `smax` mss as
                                             -- mssBegin (a:as) = 0 `smax` (a `smax` (a + mssBegin as))
                                             =: msf `smax` mss (a .: as) `smax` (meh + mssBegin (a .: as))
                                             =: qed)

  -- Now the main theorem follows easily: kadane xs = kadaneHelper xs 0 0
  -- and with meh=0, msf=0, the invariant gives us:
  --   kadaneHelper xs 0 0 = 0 `smax` mss xs `smax` (0 + mssBegin xs)
  --                       = mss xs `smax` mssBegin xs
  --                       = mss xs  (since mss xs >= mssBegin xs by definition)
  calc "correctness"
       (\(Forall xs) -> mss xs .== kadane xs) $
       \xs -> [] |- kadane xs
                 =: kadaneHelper xs 0 0
                 ?? invariant `at` (Inst @"xs" xs, Inst @"meh" (0 :: SInteger), Inst @"msf" (0 :: SInteger))
                 =: 0 `smax` mss xs `smax` (0 + mssBegin xs)
                 =: mss xs `smax` mssBegin xs
                 -- mss xs >= mssBegin xs by definition (mss considers all segments)
                 =: mss xs
                 =: qed
