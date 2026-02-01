-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.MaximumSegmentSum
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Prove that the linear version of maximum-segment-sum algorithm is
-- equivalent to the obvious version.
--
-- The maximum segment sum problem is to compute the maximum of the sum of
-- all segments of a list of arbitrary numbers. The obvious way to solve
-- this is to simply find all segments, sum them up, and calculate the maximum.
-- This has a complexity of \(O(n^3)\). However, it is possible to calculate
-- the same in linear-time, due to Kadane originally. Here we prove that
-- these algorithms are equivalent.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP          #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.MaximumSegmentSum where

import Prelude hiding (map, sum, concatMap, maximum, foldl, fst)

import Data.SBV
import Data.SBV.List
import Data.SBV.Tuple

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV
#endif

-- | The textbook definition of maximum segment sum. Note that empty list sums to 0,
-- so the maximum segment sum is always non-negative. We simply find all the segments,
-- sum them up, and pick the maximum value.
--
-- >>> mssSlow (literal [-4, -3, -7, 2, 1, -2, -1, -4])
-- 3 :: SInteger
-- >>> mssSlow (literal [-12, -6])
-- 0 :: SInteger
-- >>> mssSlow (literal [])
-- 0 :: SInteger
mssSlow :: SList Integer -> SInteger
mssSlow = maximum . map sum . segs
 where segs = concatMap tails . inits

-- | Faster version, running in linear time.
--
-- >>> mss (literal [-4, -3, -7, 2, 1, -2, -1, -4])
-- 3 :: SInteger
-- >>> mss (literal [-12, -6])
-- 0 :: SInteger
-- >>> mss (literal [])
-- 0 :: SInteger
mss :: SList Integer -> SInteger
mss = fst . foldl comb (tuple (0, 0))
 where comb :: STuple Integer Integer -> SInteger -> STuple Integer Integer
       comb (untuple -> (u, v)) x = tuple (u `smax` w, w)
         where w = (v + x) `smax` (0 :: SInteger)
