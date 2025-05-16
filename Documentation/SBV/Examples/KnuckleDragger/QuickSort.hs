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

import Prelude hiding (null, length, (++), tail, all, fst, snd, elem)
import Control.Monad.Trans (liftIO)

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
-- >>> correctness
-- Inductive lemma: lltCorrect
--   Step: Base                                                Q.E.D.
--   Step: 1                                                   Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma: lgeCorrect
--   Step: Base                                                Q.E.D.
--   Step: 1                                                   Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma: countNonNegative
--   Step: Base                                                Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                             Q.E.D.
--     Step: 1.1.2                                             Q.E.D.
--     Step: 1.2.1                                             Q.E.D.
--     Step: 1.2.2                                             Q.E.D.
--     Step: 1.Completeness                                    Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma: countElem
--   Step: Base                                                Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                             Q.E.D.
--     Step: 1.1.2                                             Q.E.D.
--     Step: 1.2.1                                             Q.E.D.
--     Step: 1.2.2                                             Q.E.D.
--     Step: 1.Completeness                                    Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma: elemCount
--   Step: Base                                                Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                               Q.E.D.
--     Step: 1.2.1                                             Q.E.D.
--     Step: 1.2.2                                             Q.E.D.
--     Step: 1.Completeness                                    Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: sublistCorrect
--   Step: 1                                                   Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: sublistElem
--   Step: 1                                                   Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: sublistTail                                          Q.E.D.
-- Lemma: permutationImpliesSublist                            Q.E.D.
-- Inductive lemma: lltSublist
--   Step: Base                                                Q.E.D.
--   Step: 1                                                   Q.E.D.
--   Step: 2                                                   Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: lltPermutation
--   Step: 1                                                   Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma: lgeSublist
--   Step: Base                                                Q.E.D.
--   Step: 1                                                   Q.E.D.
--   Step: 2                                                   Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: lgePermutation
--   Step: 1                                                   Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma: partitionFstLT
--   Step: Base                                                Q.E.D.
--   Step: 1                                                   Q.E.D.
--   Step: 2 (push llt down)                                   Q.E.D.
--   Step: 3                                                   Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma: partitionSndGE
--   Step: Base                                                Q.E.D.
--   Step: 1                                                   Q.E.D.
--   Step: 2 (push lge down)                                   Q.E.D.
--   Step: 3                                                   Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma (strong): partitionNotLongerFst
--   Step: Measure is non-negative                             Q.E.D.
--   Step: 1 (2 way full case split)
--     Step: 1.1                                               Q.E.D.
--     Step: 1.2.1                                             Q.E.D.
--     Step: 1.2.2 (simplify)                                  Q.E.D.
--     Step: 1.2.3                                             Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma (strong): partitionNotLongerSnd
--   Step: Measure is non-negative                             Q.E.D.
--   Step: 1 (2 way full case split)
--     Step: 1.1                                               Q.E.D.
--     Step: 1.2.1                                             Q.E.D.
--     Step: 1.2.2 (simplify)                                  Q.E.D.
--     Step: 1.2.3                                             Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma: countAppend
--   Step: Base                                                Q.E.D.
--   Step: 1                                                   Q.E.D.
--   Step: 2 (unfold count)                                    Q.E.D.
--   Step: 3                                                   Q.E.D.
--   Step: 4 (simplify)                                        Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma: countPartition
--   Step: Base                                                Q.E.D.
--   Step: 1 (expand partition)                                Q.E.D.
--   Step: 2 (push countTuple down)                            Q.E.D.
--   Step: 3 (2 way case split)
--     Step: 3.1.1                                             Q.E.D.
--     Step: 3.1.2 (simplify)                                  Q.E.D.
--     Step: 3.1.3                                             Q.E.D.
--     Step: 3.2.1                                             Q.E.D.
--     Step: 3.2.2 (simplify)                                  Q.E.D.
--     Step: 3.2.3                                             Q.E.D.
--     Step: 3.Completeness                                    Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma (strong): sortCountsMatch
--   Step: Measure is non-negative                             Q.E.D.
--   Step: 1 (2 way full case split)
--     Step: 1.1                                               Q.E.D.
--     Step: 1.2.1                                             Q.E.D.
--     Step: 1.2.2 (expand quickSort)                          Q.E.D.
--     Step: 1.2.3 (push count down)                           Q.E.D.
--     Step: 1.2.4                                             Q.E.D.
--     Step: 1.2.5                                             Q.E.D.
--     Step: 1.2.6 (IH on lo)                                  Q.E.D.
--     Step: 1.2.7 (IH on hi)                                  Q.E.D.
--     Step: 1.2.8                                             Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: sortIsPermutation                                    Q.E.D.
-- Inductive lemma: nonDecreasingMerge
--   Step: Base                                                Q.E.D.
--   Step: 1 (2 way full case split)
--     Step: 1.1                                               Q.E.D.
--     Step: 1.2.1                                             Q.E.D.
--     Step: 1.2.2                                             Q.E.D.
--     Step: 1.2.3                                             Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma (strong): sortIsNonDecreasing
--   Step: Measure is non-negative                             Q.E.D.
--   Step: 1 (2 way full case split)
--     Step: 1.1                                               Q.E.D.
--     Step: 1.2.1                                             Q.E.D.
--     Step: 1.2.2 (expand quickSort)                          Q.E.D.
--     Step: 1.2.3 (push nonDecreasing down)                   Q.E.D.
--     Step: 1.2.4                                             Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: quickSortIsCorrect                                   Q.E.D.
-- == Dependencies:
-- quickSortIsCorrect
--  ├╴sortIsPermutation
--  │  └╴sortCountsMatch
--  │     ├╴countAppend (x2)
--  │     ├╴partitionNotLongerFst
--  │     ├╴partitionNotLongerSnd
--  │     └╴countPartition
--  └╴sortIsNonDecreasing
--     ├╴partitionNotLongerFst
--     ├╴partitionNotLongerSnd
--     ├╴partitionFstLT
--     ├╴partitionSndGE
--     ├╴sortIsPermutation (x2)
--     ├╴lltPermutation
--     │  ├╴lltSublist
--     │  │  ├╴sublistElem
--     │  │  │  └╴sublistCorrect
--     │  │  │     ├╴countElem
--     │  │  │     │  └╴countNonNegative
--     │  │  │     └╴elemCount
--     │  │  ├╴lltCorrect
--     │  │  └╴sublistTail
--     │  └╴permutationImpliesSublist
--     ├╴lgePermutation
--     │  ├╴lgeSublist
--     │  │  ├╴sublistElem
--     │  │  ├╴lgeCorrect
--     │  │  └╴sublistTail
--     │  └╴permutationImpliesSublist
--     └╴nonDecreasingMerge
-- [Proven] quickSortIsCorrect
correctness :: IO Proof
correctness = runKDWith z3{kdOptions = (kdOptions z3) {ribbonLength = 60}} $ do

  ---------------------------------------------------------------------------------------------------
  -- Part I. Formalizing less-than/greater-than-or-equal over lists and relationship to permutations
  ---------------------------------------------------------------------------------------------------
  -- llt: list less-than:     all the elements are <  pivot
  -- lge: list greater-equal: all the elements are >= pivot
  let llt, lge :: SInteger -> SList Integer -> SBool
      llt = smtFunction "llt" $ \pivot l -> null l .|| let (x, xs) = uncons l in x .<  pivot .&& llt pivot xs
      lge = smtFunction "lge" $ \pivot l -> null l .|| let (x, xs) = uncons l in x .>= pivot .&& lge pivot xs

      -- Sublist relationship
      sublist :: SList Integer -> SList Integer -> SBool
      sublist xs ys = quantifiedBool (\(Forall @"e" e) -> count e xs .> 0 .=> count e ys .> 0)

  -- llt correctness
  lltCorrect <-
     induct "lltCorrect"
            (\(Forall @"xs" xs) (Forall @"e" e) (Forall @"pivot" pivot) -> llt pivot xs .&& e `elem` xs .=> e .< pivot) $
            \ih x xs e pivot -> [llt pivot (x .: xs), e `elem` (x .: xs)]
                             |- e .< pivot
                             ?? ih
                             =: sTrue
                             =: qed

  -- lge correctness
  lgeCorrect <-
     induct "lgeCorrect"
            (\(Forall @"xs" xs) (Forall @"e" e) (Forall @"pivot" pivot) -> lge pivot xs .&& e `elem` xs .=> e .>= pivot) $
            \ih x xs e pivot -> [lge pivot (x .: xs), e `elem` (x .: xs)]
                             |- e .>= pivot
                             ?? ih
                             =: sTrue
                             =: qed

  -- count is always non-negative
  countNonNegative <- induct "countNonNegative"
                             (\(Forall @"xs" xs) (Forall @"e" e) -> count e xs .>= 0) $
                             \ih x xs e -> [] |- count e (x .: xs) .>= 0
                                              =: cases [ e .== x ==> 1 + count e xs .>= 0
                                                                  ?? ih
                                                                  =: sTrue
                                                                  =: qed
                                                       , e ./= x ==> count e xs .>= 0
                                                                  ?? ih
                                                                  =: sTrue
                                                                  =: qed
                                                       ]

  -- relationship between count and elem, forward direction
  countElem <- induct "countElem"
                      (\(Forall @"xs" xs) (Forall @"e" e) -> e `elem` xs .=> count e xs .> 0) $
                      \ih x xs e -> [e `elem` (x .: xs)]
                                 |- count e (x .: xs) .> 0
                                 =: cases [ e .== x ==> 1 + count e xs .> 0
                                                     ?? countNonNegative
                                                     =: sTrue
                                                     =: qed
                                          , e ./= x ==> count e xs .> 0
                                                     ?? ih
                                                     =: sTrue
                                                     =: qed
                                          ]

  -- relationship between count and elem, backwards direction
  elemCount <- induct "elemCount"
                      (\(Forall @"xs" xs) (Forall @"e" e) -> count e xs .> 0 .=> e `elem` xs) $
                      \ih x xs e -> [count e xs .> 0]
                                 |- e `elem` (x .: xs)
                                 =: cases [ e .== x ==> trivial
                                          , e ./= x ==> e `elem` xs
                                                     ?? ih
                                                     =: sTrue
                                                     =: qed
                                          ]

  -- sublist correctness
  sublistCorrect <- calc "sublistCorrect"
                          (\(Forall @"xs" xs) (Forall @"ys" ys) (Forall @"x" x) -> xs `sublist` ys .&& x `elem` xs .=> x `elem` ys) $
                          \xs ys x -> [xs `sublist` ys, x `elem` xs]
                                   |- x `elem` ys
                                   ?? [ countElem `at` (Inst @"xs" xs, Inst @"e" x)
                                      , elemCount `at` (Inst @"xs" ys, Inst @"e" x)
                                      ]
                                   =: sTrue
                                   =: qed

  -- If one list is a sublist of another, then its head is an elem
  sublistElem <- calc "sublistElem"
                       (\(Forall @"x" x) (Forall @"xs" xs) (Forall @"ys" ys) -> (x .: xs) `sublist` ys .=> x `elem` ys) $
                       \x xs ys -> [(x .: xs) `sublist` ys]
                                |- x `elem` ys
                                ?? sublistCorrect `at` (Inst @"xs" (x .: xs), Inst @"ys" ys, Inst @"x" x)
                                =: sTrue
                                =: qed

  -- If one list is a sublist of another so is its tail
  sublistTail <- lemma "sublistTail"
                       (\(Forall @"x" x) (Forall @"xs" xs) (Forall @"ys" ys) -> (x .: xs) `sublist` ys .=> xs `sublist` ys)
                       []

  -- Permutation implies sublist
  permutationImpliesSublist <- lemma "permutationImpliesSublist"
                                    (\(Forall @"xs" xs) (Forall @"ys" ys) -> isPermutation xs ys .=> xs `sublist` ys)
                                    []

  -- If a value is less than all the elements in a list, then it is also less than all the elements of any sublist of it
  lltSublist <-
     inductWith cvc5 "lltSublist"
            (\(Forall @"xs" xs) (Forall @"pivot" pivot) (Forall @"ys" ys) -> llt pivot ys .&& xs `sublist` ys .=> llt pivot xs) $
            \ih x xs pivot ys -> [llt pivot ys, (x .: xs) `sublist` ys]
                              |- llt pivot (x .: xs)
                              =: x .< pivot .&& llt pivot xs
                              ?? [ -- To establish x .< pivot, observe that x is in ys, and together
                                   -- with llt pivot ys, we get that x is less than pivot
                                   sublistElem `at` (Inst @"x" x,   Inst @"xs" xs, Inst @"ys" ys)
                                 , lltCorrect `at` (Inst @"xs" ys, Inst @"e"  x,  Inst @"pivot" pivot)

                                   -- Use induction hypothesis to get rid of the second conjunct. We need to tell
                                   -- the prover that xs is a sublist of ys too so it can satisfy its precondition
                                 , sublistTail `at` (Inst @"x" x, Inst @"xs" xs, Inst @"ys" ys)
                                 , ih         `at` (Inst @"pivot" pivot, Inst @"ys" ys)
                                 ]
                              =: sTrue
                              =: qed

  -- Variant of the above for the permutation case
  lltPermutation <-
     calc "lltPermutation"
           (\(Forall @"xs" xs) (Forall @"pivot" pivot) (Forall @"ys" ys) -> llt pivot ys .&& isPermutation xs ys .=> llt pivot xs) $
           \xs pivot ys -> [llt pivot ys, isPermutation xs ys]
                        |- llt pivot xs
                        ?? [ lltSublist                `at` (Inst @"xs" xs, Inst @"pivot" pivot, Inst @"ys" ys)
                           , permutationImpliesSublist `at` (Inst @"xs" xs, Inst @"ys" ys)
                           ]
                        =: sTrue
                        =: qed

  -- If a value is greater than or equal to all the elements in a list, then it is also less than all the elements of any sublist of it
  lgeSublist <-
     inductWith cvc5 "lgeSublist"
            (\(Forall @"xs" xs) (Forall @"pivot" pivot) (Forall @"ys" ys) -> lge pivot ys .&& xs `sublist` ys .=> lge pivot xs) $
            \ih x xs pivot ys -> [lge pivot ys, (x .: xs) `sublist` ys]
                              |- lge pivot (x .: xs)
                              =: x .>= pivot .&& lge pivot xs
                              ?? [ -- To establish x .>= pivot, observe that x is in ys, and together
                                   -- with lge pivot ys, we get that x is greater than equal to the pivot
                                   sublistElem `at` (Inst @"x" x,   Inst @"xs" xs, Inst @"ys" ys)
                                 , lgeCorrect  `at` (Inst @"xs" ys, Inst @"e"  x,  Inst @"pivot" pivot)

                                   -- Use induction hypothesis to get rid of the second conjunct. We need to tell
                                   -- the prover that xs is a sublist of ys too so it can satisfy its precondition
                                 , sublistTail `at` (Inst @"x" x, Inst @"xs" xs, Inst @"ys" ys)
                                 , ih          `at` (Inst @"pivot" pivot, Inst @"ys" ys)
                                 ]
                              =: sTrue
                              =: qed

  -- Variant of the above for the permutation case
  lgePermutation <-
     calc "lgePermutation"
           (\(Forall @"xs" xs) (Forall @"pivot" pivot) (Forall @"ys" ys) -> lge pivot ys .&& isPermutation xs ys .=> lge pivot xs) $
           \xs pivot ys -> [lge pivot ys, isPermutation xs ys]
                        |- lge pivot xs
                        ?? [ lgeSublist                `at` (Inst @"xs" xs, Inst @"pivot" pivot, Inst @"ys" ys)
                           , permutationImpliesSublist `at` (Inst @"xs" xs, Inst @"ys" ys)
                           ]
                        =: sTrue
                        =: qed

  --------------------------------------------------------------------------------------------
  -- Part II. Helper lemmas for partition
  --------------------------------------------------------------------------------------------

  -- The first element of the partition produces all smaller elements
  partitionFstLT <- inductWith cvc5 "partitionFstLT"
     (\(Forall @"l" l) (Forall @"pivot" pivot) -> llt pivot (fst (partition pivot l))) $
     \ih a as pivot -> [] |- llt pivot (fst (partition pivot (a .: as)))
                          =: llt pivot (ite (a .< pivot)
                                            (a .: fst (partition pivot as))
                                            (     fst (partition pivot as)))
                          ?? "push llt down"
                          =: ite (a .< pivot)
                                 (a .< pivot .&& llt pivot (fst (partition pivot as)))
                                 (               llt pivot (fst (partition pivot as)))
                          ?? ih
                          =: sTrue
                          =: qed

  -- The second element of the partition produces all greater-than-or-equal to elements
  partitionSndGE <- inductWith cvc5 "partitionSndGE"
     (\(Forall @"l" l) (Forall @"pivot" pivot) -> lge pivot (snd (partition pivot l))) $
     \ih a as pivot -> [] |- lge pivot (snd (partition pivot (a .: as)))
                          =: lge pivot (ite (a .< pivot)
                                            (     snd (partition pivot as))
                                            (a .: snd (partition pivot as)))
                          ?? "push lge down"
                          =: ite (a .< pivot)
                                 (a .< pivot .&& lge pivot (snd (partition pivot as)))
                                 (               lge pivot (snd (partition pivot as)))
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
  -- Part III. Helper lemmas for count
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
  -- Part IV. Prove that the output of quick sort is a permutation of its input
  --------------------------------------------------------------------------------------------

  sortCountsMatch <-
     sInduct "sortCountsMatch"
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

  sortIsPermutation <- lemma "sortIsPermutation" (\(Forall @"xs" xs) -> isPermutation xs (quickSort xs)) [sortCountsMatch]

  --------------------------------------------------------------------------------------------
  -- Part V. Helper lemmas for nonDecreasing
  --------------------------------------------------------------------------------------------
  nonDecreasingMerge <-
      inductWith cvc5 "nonDecreasingMerge"
          (\(Forall @"xs" xs) (Forall @"pivot" pivot) (Forall @"ys" ys) ->
                     nonDecreasing xs .&& llt pivot xs
                 .&& nonDecreasing ys .&& lge pivot ys .=> nonDecreasing (xs ++ singleton pivot ++ ys)) $
          \ih x xs pivot ys ->
               [nonDecreasing (x .: xs), llt pivot xs, nonDecreasing ys, lge pivot ys]
            |- nonDecreasing (x .: xs ++ singleton pivot ++ ys)
            =: split xs trivial
                     (\a as -> nonDecreasing (x .: a .: as ++ singleton pivot ++ ys)
                            =: x .<= a .&& nonDecreasing (a .: as ++ singleton pivot ++ ys)
                            ?? ih
                            =: sTrue
                            =: qed)

  --------------------------------------------------------------------------------------------
  -- Part VI. Prove that the output of quick sort is non-decreasing
  --------------------------------------------------------------------------------------------
  sortIsNonDecreasing <-
     sInductWith cvc5 "sortIsNonDecreasing"
             (\(Forall @"xs" xs) -> nonDecreasing (quickSort xs))
             (length @Integer) $
             \ih xs ->
                [] |- nonDecreasing (quickSort xs)
                   =: split xs trivial
                            (\a as -> nonDecreasing (quickSort (a .: as))
                                   ?? "expand quickSort"
                                   =: nonDecreasing (let (lo, hi) = untuple (partition a as)
                                                     in quickSort lo ++ singleton a ++ quickSort hi)
                                   ?? "push nonDecreasing down"
                                   =: let (lo, hi) = untuple (partition a as)
                                   in nonDecreasing (quickSort lo ++ singleton a ++ quickSort hi)
                                   ?? [ -- Deduce that lo/hi is not longer than as, and hence, shorter than xs
                                        partitionNotLongerFst `at` (Inst @"l" as, Inst @"pivot" a)
                                      , partitionNotLongerSnd `at` (Inst @"l" as, Inst @"pivot" a)

                                        -- Use the inductive hypothesis twice to deduce quickSort of lo and hi are nonDecreasing
                                      , ih `at` (Inst @"xs" lo)  -- nonDecreasing (quickSort lo)
                                      , ih `at` (Inst @"xs" hi)  -- nonDecreasing (quickSort hi)

                                      -- Deduce that lo is all less than a, and hi is all greater than or equal to a
                                      , partitionFstLT `at` (Inst @"l" as, Inst @"pivot" a)
                                      , partitionSndGE `at` (Inst @"l" as, Inst @"pivot" a)

                                      -- Deduce that quickSort lo is all less than a
                                      , sortIsPermutation `at`  Inst @"xs" lo
                                      , lltPermutation    `at` (Inst @"xs" (quickSort lo), Inst @"pivot" a, Inst @"ys" lo)

                                      -- Deduce that quickSort hi is all greater than or equal to a
                                      , sortIsPermutation `at`  Inst @"xs" hi
                                      , lgePermutation    `at` (Inst @"xs" (quickSort hi), Inst @"pivot" a, Inst @"ys" hi)

                                      -- Finally conclude that the whole reconstruction is non-decreasing
                                      , nonDecreasingMerge `at` (Inst @"xs" (quickSort lo), Inst @"pivot" a, Inst @"ys" (quickSort hi))
                                      ]
                                   =: sTrue
                                   =: qed)

  --------------------------------------------------------------------------------------------
  -- Part VII. Putting it together
  --------------------------------------------------------------------------------------------

  qs <- lemma "quickSortIsCorrect"
           (\(Forall @"xs" xs) -> let out = quickSort xs in isPermutation xs out .&& nonDecreasing out)
           [sortIsPermutation, sortIsNonDecreasing]

  -- | We can display the dependencies in a proof
  liftIO $ do putStrLn "== Dependencies:"
              putStr $ show $ getProofTree qs

  pure qs
