-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.QuickSort
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving quick sort correct.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.QuickSort where

import Prelude hiding (null, (++), head, tail, elem, notElem, fst, snd, length)

import Data.SBV
import Data.SBV.List hiding (partition)
import Data.SBV.Tuple
import Data.SBV.Tools.KnuckleDragger

-- * Quick sort

-- | Quick-sort, using the first element as pivot.
quickSort :: SList Integer -> SList Integer
quickSort = smtFunction "quickSort" $ \l -> ite (null l)
                                                nil
                                                (let (x,  xs) = uncons l
                                                     (lo, hi) = untuple (partition x xs)
                                                 in  quickSort lo ++ singleton x ++ quickSort hi)

-- | We define @partition@ as an explicit function. Unfortunately, we can't just replace this
-- with @\pivot xs -> Data.List.SBV.partition (.<= pivot) xs@ because that would create a firstified version of partition
-- with a free-variable captured, which isn't supported due to higher-order limitations in SMTLib.
partition :: SInteger -> SList Integer -> STuple [Integer] [Integer]
partition = smtFunction "split" $ \pivot xs -> ite (null xs)
                                                   (tuple (nil, nil))
                                                   (let (a,  as) = uncons xs
                                                        (lo, hi) = untuple (partition pivot as)
                                                    in ite (a .<= pivot)
                                                           (tuple (a .: lo, hi))
                                                           (tuple (lo, a .: hi)))

-- * Helper functions

-- | A predicate testing whether a given list is non-decreasing.
nonDecreasing :: SList Integer -> SBool
nonDecreasing = smtFunction "nonDecreasing" $ \l ->  null l .|| null (tail l)
                                                 .|| let (x, l') = uncons l
                                                         (y, _)  = uncons l'
                                                     in x .<= y .&& nonDecreasing l'

-- | Count the number of occurrences of an element in a list
count :: SInteger -> SList Integer -> SInteger
count = smtFunction "count" $ \e l -> ite (null l)
                                          0
                                          (let (x, xs) = uncons l
                                               cxs     = count e xs
                                           in ite (e .== x) (1 + cxs) cxs)

-- | Are two lists permutations of each other?
isPermutation :: SList Integer -> SList Integer -> SBool
isPermutation xs ys = quantifiedBool (\(Forall @"x" x) -> count x xs .== count x ys)

-- * Correctness proof

-- | Correctness of quick-sort.
--
-- We have:
--
-- >>> correctness
correctness :: IO Proof
correctness = runKDWith z3{kdOptions = (kdOptions z3) {ribbonLength = 60}} $ do

  --------------------------------------------------------------------------------------------
  -- Part I. Prove that the output of quick sort is a permutation of its input
  --------------------------------------------------------------------------------------------

  countAppend <-
      induct "countAppend"
             (\(Forall @"xs" xs) (Forall @"ys" ys) (Forall @"e" e) -> count e (xs ++ ys) .== count e xs + count e ys) $
             \ih x xs ys e -> [] |- count e ((x .: xs) ++ ys)
                                 =: count e (x .: (xs ++ ys))
                                 ?? "unfold count"
                                 =: (let r = count e (xs ++ ys) in ite (e .== x) (1+r) r)
                                 ?? ih `at` (Inst @"ys" ys, Inst @"e" e)
                                 =: (let r = count e xs + count e ys in ite (e .== x) (1+r) r)
                                 ?? "simplify"
                                 =: count e (x .: xs) + count e ys
                                 =: qed

  partitionLoSize <-
      lemma "partitionLoSize"
            (\(Forall @"l" l) (Forall @"pivot" pivot) -> length (fst (partition pivot l)) .<= length l)
            [sorry]

  _artitionHiSize <-
      lemma "partitionHiSize"
            (\(Forall @"l" l) (Forall @"pivot" pivot) -> length (snd (partition pivot l)) .<= length l)
            [sorry]

  countPartitionLT <-
      sInduct  "countPartitionLT"
               (\(Forall @"l" l) (Forall @"pivot" pivot) (Forall @"e" e) ->
                      count e (fst (partition pivot l)) .== ite (e .<= pivot) (count e l) 0)
               (\l (_ :: SInteger) (_ :: SInteger) -> length @Integer l) $
               \ih l pivot e ->
                   [] |- split l trivial
                               (\a as -> count e (fst (partition pivot (a .: as)))
                                      ?? "unfold count/partition"
                                      =: let lo = fst (partition pivot as)
                                      in count e (ite (a .<= pivot) (a .: lo) lo)
                                      ?? [ ih              `at` (Inst @"l" as, Inst @"pivot" pivot, Inst @"e" e)
                                         , partitionLoSize `at` (Inst @"l" as, Inst @"pivot" pivot)
                                         ]
                                      =: ite (e .<= pivot) (count e (a .: lo)) 0
                                      =: qed)


  error "stop here" countAppend countPartitionLT

{-
lemma count_filter_le:
  "count x (filter (λy. y ≤ z) xs) = (if x ≤ z then count x xs else Z)"
  apply (induction xs)
   apply auto
  done

lemma count_filter_gt:
  "count x (filter (λy. z < y) xs) = (if z < x then count x xs else Z)"
  apply (induction xs)
   apply auto
  done

theorem quicksort_perm: "perm (quicksort xs) xs"
proof (induction xs)
  case Nil
  then show ?case by (simp add: perm_def)
next
  case (Cons x xs)
  let ?L = "filter (λy. y ≤ x) xs"
  let ?R = "filter (λy. x < y) xs"
  have "perm (quicksort xs) (quicksort ?L @ Cons x (quicksort ?R))" by simp
  also have "perm … (?L @ Cons x ?R)"
    using Cons.IH by (auto simp: perm_def count_app count_filter_le count_filter_gt)
  also have "perm … (Cons x xs)"
    unfolding perm_def
    by (auto simp: count.simps count_filter_le count_filter_gt count_app)
  finally show ?case .
qed

theorem quicksort_sorted: "sorted (quicksort xs)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  let ?L = "quicksort (filter (λy. y ≤ x) xs)"
  let ?R = "quicksort (filter (λy. x < y) xs)"
  have L: "sorted ?L" using Cons.IH(1) by simp
  have R: "sorted ?R" using Cons.IH(2) by simp
  show ?case
  proof (cases ?L)
    case Nil
    then show ?thesis using R by simp
  next
    case (Cons l1 lxs)
    have "sorted (?L @ Cons x ?R)" using L R
      by (auto simp: sorted.simps)
    then show ?thesis by simp
  qed
qed

end
-}
