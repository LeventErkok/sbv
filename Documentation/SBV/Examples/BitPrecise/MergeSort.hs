-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.BitPrecise.MergeSort
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Symbolic implementation of merge-sort and its correctness.
-----------------------------------------------------------------------------

{-# LANGUAGE TupleSections #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.BitPrecise.MergeSort where

import Data.SBV
import Data.SBV.Tools.CodeGen

-----------------------------------------------------------------------------
-- * Implementing Merge-Sort
-----------------------------------------------------------------------------
-- | Element type of lists we'd like to sort. For simplicity, we'll just
-- use 'SWord8' here, but we can pick any symbolic type.
type E = SWord8

-- | Merging two given sorted lists, preserving the order.
merge :: [E] -> [E] -> [E]
merge []     ys           = ys
merge xs     []           = xs
merge xs@(x:xr) ys@(y:yr) = ite (x .< y) (x : merge xr ys) (y : merge xs yr)

-- | Simple merge-sort implementation. We simply divide the input list
-- in two halves so long as it has at least two elements, sort
-- each half on its own, and then merge.
mergeSort :: [E] -> [E]
mergeSort []  = []
mergeSort [x] = [x]
mergeSort xs  = merge (mergeSort th) (mergeSort bh)
   where (th, bh) = splitAt (length xs `div` 2) xs

-----------------------------------------------------------------------------
-- * Proving correctness
-- ${props}
-----------------------------------------------------------------------------
{- $props
There are two main parts to proving that a sorting algorithm is correct:

       * Prove that the output is non-decreasing
 
       * Prove that the output is a permutation of the input
-}

-- | Check whether a given sequence is non-decreasing.
nonDecreasing :: [E] -> SBool
nonDecreasing []       = sTrue
nonDecreasing [_]      = sTrue
nonDecreasing (a:b:xs) = a .<= b .&& nonDecreasing (b:xs)

-- | Check whether two given sequences are permutations. We simply check that each sequence
-- is a subset of the other, when considered as a set. The check is slightly complicated
-- for the need to account for possibly duplicated elements.
isPermutationOf :: [E] -> [E] -> SBool
isPermutationOf as bs = go as (map (, sTrue) bs) .&& go bs (map (, sTrue) as)
  where go []     _  = sTrue
        go (x:xs) ys = let (found, ys') = mark x ys in found .&& go xs ys'
        -- Go and mark off an instance of 'x' in the list, if possible. We keep track
        -- of unmarked elements by associating a boolean bit. Note that we have to
        -- keep the lists equal size for the recursive result to merge properly.
        mark _ []         = (sFalse, [])
        mark x ((y,v):ys) = ite (v .&& x .== y)
                                (sTrue, (y, sNot v):ys)
                                (let (r, ys') = mark x ys in (r, (y,v):ys'))

-- | Asserting correctness of merge-sort for a list of the given size. Note that we can
-- only check correctness for fixed-size lists. Also, the proof will get more and more
-- complicated for the backend SMT solver as the list size increases. A value around
-- 5 or 6 should be fairly easy to prove. For instance, we have:
--
-- >>> correctness 5
-- Q.E.D.
correctness :: Int -> IO ThmResult
correctness n = prove $ do xs <- mkFreeVars n
                           let ys = mergeSort xs
                           return $ nonDecreasing ys .&& isPermutationOf xs ys

-----------------------------------------------------------------------------
-- * Generating C code
-----------------------------------------------------------------------------

-- | Generate C code for merge-sorting an array of size @n@. Again, we're restricted
-- to fixed size inputs. While the output is not how one would code merge sort in C
-- by hand, it's a faithful rendering of all the operations merge-sort would do as
-- described by its Haskell counterpart.
codeGen :: Int -> IO ()
codeGen n = compileToC (Just ("mergeSort" ++ show n)) "mergeSort" $ do
                xs <- cgInputArr n "xs"
                cgOutputArr "ys" (mergeSort xs)
