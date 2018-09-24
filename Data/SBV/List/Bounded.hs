-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.List.Bounded
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- A collection of bounded list utilities, useful when working with symbolic lists.
-- These functions all take a concrete bound, and operate on the prefix of a symbolic
-- list that is at most that long. Due to limitations on writing recursive functions
-- over lists (the classic symbolic termination problem), we cannot write arbitrary
-- recursive programs on symbolic lists. But most of the time all we need is a
-- bounded prefix of this list, at which point these functions come in handy.
-----------------------------------------------------------------------------
--
{-# LANGUAGE OverloadedLists #-}

module Data.SBV.List.Bounded (
     -- * General folds
     bfoldr, bfoldl
     -- * Map, filter, zipWith, elem
   , bmap, bfilter, bzipWith, belem
     -- * Aggregates
   , bsum, bprod, band, bor, bany, ball, bmaximum, bminimum
   )
   where

import Data.SBV
import Data.SBV.List ((.:))
import qualified Data.SBV.List as L

-- | Case analysis on a symbolic list. (Not exported.)
lcase :: (SymWord a, Mergeable b) => SList a -> b -> (SBV a -> SList a -> b) -> b
lcase s e c = ite (L.null s) e (c (L.head s) (L.tail s))

-- | Bounded fold from the right.
bfoldr :: (SymWord a, SymWord b) => Int -> (SBV a -> SBV b -> SBV b) -> SBV b -> SList a -> SBV b
bfoldr cnt f b = go (cnt `max` 0)
  where go 0 _ = b
        go i s = lcase s b (\h t -> h `f` go (i-1) t)

-- | Bounded fold from the left.
bfoldl :: (SymWord a, SymWord b) => Int -> (SBV b -> SBV a -> SBV b) -> SBV b -> SList a -> SBV b
bfoldl cnt f = go (cnt `max` 0)
  where go 0 b _ = b
        go i b s = lcase s b (\h t -> go (i-1) (b `f` h) t)

-- | Bounded sum.
bsum :: (SymWord a, Num a) => Int -> SList a -> SBV a
bsum i = bfoldl i (+) 0

-- | Bounded product.
bprod :: (SymWord a, Num a) => Int -> SList a -> SBV a
bprod i = bfoldl i (*) 1

-- | Bounded map.
bmap :: (SymWord a, SymWord b) => Int -> (SBV a -> SBV b) -> SList a -> SList b
bmap i f = bfoldr i (\x -> (f x .:)) []

-- | Bounded filter.
bfilter :: SymWord a => Int -> (SBV a -> SBool) -> SList a -> SList a
bfilter i f = bfoldr i (\x y -> ite (f x) (x .: y) y) []

-- | Bounded logical and
band :: Int -> SList Bool -> SBool
band i = bfoldr i (&&&) (true  :: SBool)

-- | Bounded logical or
bor :: Int -> SList Bool -> SBool
bor i = bfoldr i (|||) (false :: SBool)

-- | Bounded any
bany :: SymWord a => Int -> (SBV a -> SBool) -> SList a -> SBool
bany i f = bor i . bmap i f

-- | Bounded all
ball :: SymWord a => Int -> (SBV a -> SBool) -> SList a -> SBool
ball i f = band i . bmap i f

-- | Bounded maximum. Undefined if list is empty.
bmaximum :: (SymWord a, Num a) => Int -> SList a -> SBV a
bmaximum i l = bfoldl (i-1) smax (L.head l) (L.tail l)

-- | Bounded minimum. Undefined if list is empty.
bminimum :: (SymWord a, Num a) => Int -> SList a -> SBV a
bminimum i l = bfoldl (i-1) smin (L.head l) (L.tail l)

-- | Bounded zipWith
bzipWith :: (SymWord a, SymWord b, SymWord c) => Int -> (SBV a -> SBV b -> SBV c) -> SList a -> SList b -> SList c
bzipWith cnt f = go (cnt `max` 0)
   where go 0 _  _  = []
         go i xs ys = ite (L.null xs ||| L.null ys)
                          []
                          (f (L.head xs) (L.head ys) .: go (i-1) (L.tail xs) (L.tail ys))

-- | Bounded element check
belem :: SymWord a => Int -> SBV a -> SList a -> SBool
belem i e = bany i (e .==)
