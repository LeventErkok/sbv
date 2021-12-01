-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.BoundedList
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A collection of bounded list utilities, useful when working with symbolic lists.
-- These functions all take a concrete bound, and operate on the prefix of a symbolic
-- list that is at most that long. Due to limitations on writing recursive functions
-- over lists (the classic symbolic termination problem), we cannot write arbitrary
-- recursive programs on symbolic lists. But most of the time all we need is a
-- bounded prefix of this list, at which point these functions come in handy.
-----------------------------------------------------------------------------

{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.BoundedList (
     -- * General folds
     bfoldr, bfoldrM, bfoldl, bfoldlM
     -- * Map, filter, zipWith, elem
   , bmap, bmapM, bfilter, bzipWith, belem
     -- * Aggregates
   , bsum, bprod, band, bor, bany, ball, bmaximum, bminimum
     -- * Miscellaneous: Reverse and sort
   , breverse, bsort
   )
   where

import Prelude hiding ((++))

import Data.SBV
import Data.SBV.List ((.:), (++))
import qualified Data.SBV.List as L

-- | Case analysis on a symbolic list. (Not exported.)
lcase :: (SymVal a, Mergeable b) => SList a -> b -> (SBV a -> SList a -> b) -> b
lcase s e c = ite (L.null s) e (c (L.head s) (L.tail s))

-- | Bounded fold from the right.
bfoldr :: (SymVal a, SymVal b) => Int -> (SBV a -> SBV b -> SBV b) -> SBV b -> SList a -> SBV b
bfoldr cnt f b = go (cnt `max` 0)
  where go 0 _ = b
        go i s = lcase s b (\h t -> h `f` go (i-1) t)

-- | Bounded monadic fold from the right.
bfoldrM :: forall a b m. (SymVal a, SymVal b, Monad m, Mergeable (m (SBV b)))
        => Int -> (SBV a -> SBV b -> m (SBV b)) -> SBV b -> SList a -> m (SBV b)
bfoldrM cnt f b = go (cnt `max` 0)
  where go :: Int -> SList a -> m (SBV b)
        go 0 _ = return b
        go i s = lcase s (return b) (\h t -> f h =<< go (i-1) t)

-- | Bounded fold from the left.
bfoldl :: (SymVal a, SymVal b) => Int -> (SBV b -> SBV a -> SBV b) -> SBV b -> SList a -> SBV b
bfoldl cnt f = go (cnt `max` 0)
  where go 0 b _ = b
        go i b s = lcase s b (\h t -> go (i-1) (b `f` h) t)

-- | Bounded monadic fold from the left.
bfoldlM :: forall a b m. (SymVal a, SymVal b, Monad m, Mergeable (m (SBV b)))
        => Int -> (SBV b -> SBV a -> m (SBV b)) -> SBV b -> SList a -> m (SBV b)
bfoldlM cnt f = go (cnt `max` 0)
  where go :: Int -> SBV b -> SList a -> m (SBV b)
        go 0 b _ = return b
        go i b s = lcase s (return b) (\h t -> do { fbh <- f b h; go (i-1) fbh t })

-- | Bounded sum.
bsum :: (SymVal a, Num a, Ord a) => Int -> SList a -> SBV a
bsum i = bfoldl i (+) 0

-- | Bounded product.
bprod :: (SymVal a, Num a, Ord a) => Int -> SList a -> SBV a
bprod i = bfoldl i (*) 1

-- | Bounded map.
bmap :: (SymVal a, SymVal b) => Int -> (SBV a -> SBV b) -> SList a -> SList b
bmap i f = bfoldr i (\x -> (f x .:)) []

-- | Bounded monadic map.
bmapM :: (SymVal a, SymVal b, Monad m, Mergeable (m (SBV [b])))
      => Int -> (SBV a -> m (SBV b)) -> SList a -> m (SList b)
bmapM i f = bfoldrM i (\a bs -> (.:) <$> f a <*> pure bs) []

-- | Bounded filter.
bfilter :: SymVal a => Int -> (SBV a -> SBool) -> SList a -> SList a
bfilter i f = bfoldr i (\x y -> ite (f x) (x .: y) y) []

-- | Bounded logical and
band :: Int -> SList Bool -> SBool
band i = bfoldr i (.&&) (sTrue  :: SBool)

-- | Bounded logical or
bor :: Int -> SList Bool -> SBool
bor i = bfoldr i (.||) (sFalse :: SBool)

-- | Bounded any
bany :: SymVal a => Int -> (SBV a -> SBool) -> SList a -> SBool
bany i f = bor i . bmap i f

-- | Bounded all
ball :: SymVal a => Int -> (SBV a -> SBool) -> SList a -> SBool
ball i f = band i . bmap i f

-- | Bounded maximum. Undefined if list is empty.
bmaximum :: (Ord a, SymVal a) => Int -> SList a -> SBV a
bmaximum i l = bfoldl (i-1) smax (L.head l) (L.tail l)

-- | Bounded minimum. Undefined if list is empty.
bminimum :: (Ord a, SymVal a) => Int -> SList a -> SBV a
bminimum i l = bfoldl (i-1) smin (L.head l) (L.tail l)

-- | Bounded zipWith
bzipWith :: (SymVal a, SymVal b, SymVal c) => Int -> (SBV a -> SBV b -> SBV c) -> SList a -> SList b -> SList c
bzipWith cnt f = go (cnt `max` 0)
   where go 0 _  _  = []
         go i xs ys = ite (L.null xs .|| L.null ys)
                          []
                          (f (L.head xs) (L.head ys) .: go (i-1) (L.tail xs) (L.tail ys))

-- | Bounded element check
belem :: (Eq a, SymVal a) => Int -> SBV a -> SList a -> SBool
belem i e = bany i (e .==)

-- | Bounded reverse
breverse :: SymVal a => Int -> SList a -> SList a
breverse cnt = bfoldr cnt (\a b -> b ++ L.singleton a) []

-- | Bounded paramorphism (not exported).
bpara :: (SymVal a, SymVal b) => Int -> (SBV a -> SBV [a] -> SBV b -> SBV b) -> SBV b -> SList a -> SBV b
bpara cnt f b = go (cnt `max` 0)
  where go 0 _ = b
        go i s = lcase s b (\h t -> f h t (go (i-1) t))

-- | Insert an element into a sorted list (not exported).
binsert :: (Ord a, SymVal a) => Int -> SBV a -> SList a -> SList a
binsert cnt a = bpara cnt f (L.singleton a)
  where f sortedHd sortedTl sortedTl' = ite (a .< sortedHd)
                                            (a .: sortedHd .: sortedTl)
                                            (sortedHd .: sortedTl')

-- | Bounded insertion sort
bsort :: (Ord a, SymVal a) => Int -> SList a -> SList a
bsort cnt = bfoldr cnt (binsert cnt) []
