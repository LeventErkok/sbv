-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.QuickSort
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving quick sort correct. The proof here closely follows the development
-- given by Tobias Nipkow, in his paper  "Term Rewriting and Beyond -- Theorem
-- Proving in Isabelle," published in Formal Aspects of Computing 1: 320-338
-- back in 1989.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.QuickSort where

import Prelude hiding (null, length, (++), tail, all, fst, snd)

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
-- with @\pivot xs -> Data.List.SBV.partition (.< pivot) xs@ because that would create a firstified version of partition
-- with a free-variable captured, which isn't supported due to higher-order limitations in SMTLib.
partition :: SInteger -> SList Integer -> STuple [Integer] [Integer]
partition = smtFunction "partition" $ \pivot xs -> ite (null xs)
                                                       (tuple (nil, nil))
                                                       (let (a,  as) = uncons xs
                                                            (lo, hi) = untuple (partition pivot as)
                                                        in ite (a .< pivot)
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
-- correctness
correctness :: IO Proof
correctness = runKDWith z3{kdOptions = (kdOptions z3) {ribbonLength = 60}} $ do

  --------------------------------------------------------------------------------------------
  -- Part I. Helper lemmas for partition
  --------------------------------------------------------------------------------------------

  -- lt: the element is less than all the elements in the list
  -- ge: the element is greater than or equal to all the elements in the list
  let lt, ge :: SInteger -> SList Integer -> SBool
      lt = smtFunction "lt" $ \pivot l -> null l .|| let (x, xs) = uncons l in x .<  pivot .&& lt pivot xs
      ge = smtFunction "ge" $ \pivot l -> null l .|| let (x, xs) = uncons l in x .>= pivot .&& ge pivot xs

  -- The first element of the partition produces all smaller elements
  partitionFstLT <- inductWith cvc5 "partitionFstLT"
     (\(Forall @"l" l) (Forall @"pivot" pivot) -> lt pivot (fst (partition pivot l))) $
     \ih a as pivot -> [] |- lt pivot (fst (partition pivot (a .: as)))
                          =: lt pivot (ite (a .< pivot)
                                           (a .: fst (partition pivot as))
                                           (fst (partition pivot as)))
                          ?? "push lt down"
                          =: ite (a .< pivot)
                                 (a .< pivot .&& lt pivot (fst (partition pivot as)))
                                 (               lt pivot (fst (partition pivot as)))
                          ?? ih
                          =: sTrue
                          =: qed

  -- The second element of the partition produces all greater-than-or-equal to elements
  partitionSndGE <- inductWith cvc5 "partitionSndGE"
     (\(Forall @"l" l) (Forall @"pivot" pivot) -> ge pivot (snd (partition pivot l))) $
     \ih a as pivot -> [] |- ge pivot (snd (partition pivot (a .: as)))
                          =: ge pivot (ite (a .< pivot)
                                           (     snd (partition pivot as))
                                           (a .: snd (partition pivot as)))
                          ?? "push ge down"
                          =: ite (a .< pivot)
                                 (a .< pivot .&& ge pivot (snd (partition pivot as)))
                                 (               ge pivot (snd (partition pivot as)))
                          ?? ih
                          =: sTrue
                          =: qed

  -- The first element of partition does not increase in size
  partitionNotLongerFst <- sInduct "partitionNotLongerFst"
     (\(Forall @"l" l) (Forall @"pivot" pivot) -> length (fst (partition pivot l)) .<= length l)
     (\l (_ :: SInteger) -> length @Integer l) $
     (\ih l pivot -> [] |- length (fst (partition pivot l)) .<= length l
                        =: split l trivial
                                 (\a as -> let lo = fst (partition pivot as)
                                        in ite (a .< pivot)
                                               (length (a .: lo) .<= length (a .: as))
                                               (length       lo  .<= length (a .: as))
                                        ?? "simplify"
                                        =: ite (a .< pivot)
                                               (length lo .<=     length as)
                                               (length lo .<= 1 + length as)
                                        ?? ih `at` (Inst @"l" as, Inst @"pivot" pivot)
                                        =: sTrue
                                        =: qed))

  -- The second element of partition does not increase in size
  partitionNotLongerSnd <- sInduct "partitionNotLongerSnd"
     (\(Forall @"l" l) (Forall @"pivot" pivot) -> length (snd (partition pivot l)) .<= length l)
     (\l (_ :: SInteger) -> length @Integer l) $
     (\ih l pivot -> [] |- length (snd (partition pivot l)) .<= length l
                        =: split l trivial
                                 (\a as -> let hi = snd (partition pivot as)
                                        in ite (a .< pivot)
                                               (length       hi  .<= length (a .: as))
                                               (length (a .: hi) .<= length (a .: as))
                                        ?? "simplify"
                                        =: ite (a .< pivot)
                                               (length hi .<= 1 + length as)
                                               (length hi .<=     length as)
                                        ?? ih `at` (Inst @"l" as, Inst @"pivot" pivot)
                                        =: sTrue
                                        =: qed))

  --------------------------------------------------------------------------------------------
  -- Part II. Helper lemmas for count
  --------------------------------------------------------------------------------------------

  -- Count distributes over append
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


  -- Count is preserved over partition
  let countTuple :: SInteger -> STuple [Integer] [Integer] -> SInteger
      countTuple e xsys = count e xs + count e ys
        where (xs, ys) = untuple xsys

  countPartition <-
     induct "countPartition"
            (\(Forall @"xs" xs) (Forall @"pivot" pivot) (Forall @"e" e) -> countTuple e (partition pivot xs) .== count e xs) $
            \ih a as pivot e ->
                [] |- countTuple e (partition pivot (a .: as))
                   ?? "expand partition"
                   =: countTuple e (let (lo, hi) = untuple (partition pivot as)
                                    in ite (a .< pivot)
                                           (tuple (a .: lo, hi))
                                           (tuple (lo, a .: hi)))
                   ?? "push countTuple down"
                   =: let (lo, hi) = untuple (partition pivot as)
                   in ite (a .< pivot)
                          (count e (a .: lo) + count e hi)
                          (count e lo + count e (a .: hi))
                   =: cases [e .== a  ==> ite (a .< pivot)
                                              (1 + count e lo + count e hi)
                                              (count e lo + 1 + count e hi)
                                       ?? "simplify"
                                       =: 1 + count e lo + count e hi
                                       ?? ih
                                       =: 1 + count e as
                                       =: qed
                            , e ./= a ==> ite (a .< pivot)
                                              (count e lo + count e hi)
                                              (count e lo + count e hi)
                                       ?? "simplify"
                                       =: count e lo + count e hi
                                       ?? ih
                                       =: count e as
                                       =: qed
                            ]


  --------------------------------------------------------------------------------------------
  -- Part III. Prove that the output of quick sort is a permutation of its input
  --------------------------------------------------------------------------------------------

  sortIsPermutation <-
     sInduct "sortIsPermutation"
             (\(Forall @"xs" xs) (Forall @"e" e) -> count e xs .== count e (quickSort xs))
             (\xs (_ :: SInteger) -> length @Integer xs) $
             \ih xs e ->
                [] |- count e (quickSort xs)
                   =: split xs trivial
                            (\a as -> count e (quickSort (a .: as))
                                   ?? "expand quickSort"
                                   =: count e (let (lo, hi) = untuple (partition a as)
                                               in quickSort lo ++ singleton a ++ quickSort hi)
                                   ?? "push count down"
                                   =: let (lo, hi) = untuple (partition a as)
                                   in count e (quickSort lo ++ singleton a ++ quickSort hi)
                                   ?? countAppend `at` (Inst @"xs" (quickSort lo), Inst @"ys" (singleton a ++ quickSort hi), Inst @"e" e)
                                   =: count e (quickSort lo) + count e (singleton a ++ quickSort hi)
                                   ?? countAppend `at` (Inst @"xs" (singleton a), Inst @"ys" (quickSort hi), Inst @"e" e)
                                   =: count e (quickSort lo) + count e (singleton a) + count e (quickSort hi)
                                   ?? [ hprf  $ ih                    `at` (Inst @"xs" lo, Inst @"e" e)
                                      , hprf  $ partitionNotLongerFst `at` (Inst @"l"  as, Inst @"pivot" a)
                                      , hasm  $ xs .== a .: as
                                      , hcmnt $ "IH on lo"
                                      ]
                                   =: count e lo + count e (singleton a) + count e (quickSort hi)
                                   ?? [ hprf  $ ih                    `at` (Inst @"xs" hi, Inst @"e" e)
                                      , hprf  $ partitionNotLongerSnd `at` (Inst @"l"  as, Inst @"pivot" a)
                                      , hasm  $ xs .== a .: as
                                      , hcmnt $ "IH on hi"
                                      ]
                                   =: count e lo + count e (singleton a) + count e hi
                                   ?? countPartition `at` (Inst @"xs" as, Inst @"pivot" a, Inst @"e" e)
                                   =: count e xs
                                   =: qed)

  --------------------------------------------------------------------------------------------
  -- Part IV. Prove that the output of quick sort is non-decreasing
  --------------------------------------------------------------------------------------------
  sortIsNonDecreasing <-
     lemma   "sortIsNonDecreasing"
             (\(Forall @"xs" xs) -> nonDecreasing (quickSort xs))
             [sorry]

  --------------------------------------------------------------------------------------------
  -- Part V. Putting it together
  --------------------------------------------------------------------------------------------

  _ <- lemma "quickSortIsCorrect"
        (\(Forall @"xs" xs) -> let out = quickSort xs in isPermutation xs out .&& nonDecreasing out)
        [sortIsPermutation, sortIsNonDecreasing]

  error "stop here" partitionFstLT partitionSndGE
