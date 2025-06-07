-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.QuickSort
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

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.QuickSort where

import Prelude hiding (null, length, (++), tail, all, fst, snd, elem)
import Control.Monad.Trans (liftIO)
import Data.Proxy

import Data.SBV
import Data.SBV.List hiding (partition)
import Data.SBV.Tuple
import Data.SBV.Tools.TP
import qualified Data.SBV.Tools.TP.List as TP

import qualified Documentation.SBV.Examples.TP.SortHelpers as SH

#ifdef DOCTEST
-- $setup
-- >>> :set -XTypeApplications
-- >>> import Data.Proxy
#endif

-- * Quick sort

-- | Quick-sort, using the first element as pivot.
quickSort :: (Ord a, SymVal a) => SList a -> SList a
quickSort = smtFunction "quickSort" $ \l -> ite (null l)
                                                nil
                                                (let (x,  xs) = uncons l
                                                     (lo, hi) = untuple (partition x xs)
                                                 in  quickSort lo ++ singleton x ++ quickSort hi)

-- | We define @partition@ as an explicit function. Unfortunately, we can't just replace this
-- with @\pivot xs -> Data.List.SBV.partition (.< pivot) xs@ because that would create a firstified version of partition
-- with a free-variable captured, which isn't supported due to higher-order limitations in SMTLib.
partition :: (Ord a, SymVal a) => SBV a -> SList a -> STuple [a] [a]
partition = smtFunction "partition" $ \pivot xs -> ite (null xs)
                                                       (tuple (nil, nil))
                                                       (let (a,  as) = uncons xs
                                                            (lo, hi) = untuple (partition pivot as)
                                                        in ite (a .< pivot)
                                                               (tuple (a .: lo, hi))
                                                               (tuple (lo, a .: hi)))

-- * Correctness proof

-- | Correctness of quick-sort.
--
-- We have:
--
-- >>> correctness (Proxy @Integer)
-- Inductive lemma: countAppend @Integer
--   Step: Base                                                Q.E.D.
--   Step: 1                                                   Q.E.D.
--   Step: 2 (unfold count)                                    Q.E.D.
--   Step: 3                                                   Q.E.D.
--   Step: 4 (simplify)                                        Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma: countNonNeg @Integer
--   Step: Base                                                Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                             Q.E.D.
--     Step: 1.1.2                                             Q.E.D.
--     Step: 1.2.1                                             Q.E.D.
--     Step: 1.2.2                                             Q.E.D.
--     Step: 1.Completeness                                    Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma: countElem @Integer
--   Step: Base                                                Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                                             Q.E.D.
--     Step: 1.1.2                                             Q.E.D.
--     Step: 1.2.1                                             Q.E.D.
--     Step: 1.2.2                                             Q.E.D.
--     Step: 1.Completeness                                    Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma: elemCount @Integer
--   Step: Base                                                Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                               Q.E.D.
--     Step: 1.2.1                                             Q.E.D.
--     Step: 1.2.2                                             Q.E.D.
--     Step: 1.Completeness                                    Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: sublistCorrect @Integer
--   Step: 1                                                   Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: sublistElem @Integer
--   Step: 1                                                   Q.E.D.
--   Result:                                                   Q.E.D.
-- Lemma: sublistTail @Integer                                 Q.E.D.
-- Lemma: sublistIfPerm @Integer                               Q.E.D.
-- Inductive lemma: lltCorrect
--   Step: Base                                                Q.E.D.
--   Step: 1                                                   Q.E.D.
--   Result:                                                   Q.E.D.
-- Inductive lemma: lgeCorrect
--   Step: Base                                                Q.E.D.
--   Step: 1                                                   Q.E.D.
--   Result:                                                   Q.E.D.
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
-- Lemma: quickSortIsCorrect @Integer                          Q.E.D.
-- == Proof tree:
-- quickSortIsCorrect @Integer
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
--     │  │  │     │  └╴countNonNeg @Integer
--     │  │  │     └╴elemCount
--     │  │  ├╴lltCorrect
--     │  │  └╴sublistTail
--     │  └╴sublistIfPerm
--     ├╴lgePermutation
--     │  ├╴lgeSublist
--     │  │  ├╴sublistElem
--     │  │  ├╴lgeCorrect
--     │  │  └╴sublistTail
--     │  └╴sublistIfPerm
--     └╴nonDecreasingMerge
-- [Proven] quickSortIsCorrect @Integer
correctness :: forall a. (Ord a, SymVal a) => Proxy a -> IO Proof
correctness p = runTPWith (tpRibbon 60 z3) $ do

  --------------------------------------------------------------------------------------------
  -- Part I. Import helper lemmas, definitions
  --------------------------------------------------------------------------------------------
  let count         = TP.count         @a
      isPermutation = SH.isPermutation @a
      nonDecreasing = SH.nonDecreasing @a
      sublist       = SH.sublist       @a

  countAppend   <- TP.countAppend   p
  sublistElem   <- SH.sublistElem   p
  sublistTail   <- SH.sublistTail   p
  sublistIfPerm <- SH.sublistIfPerm p

  ---------------------------------------------------------------------------------------------------
  -- Part II. Formalizing less-than/greater-than-or-equal over lists and relationship to permutations
  ---------------------------------------------------------------------------------------------------
  -- llt: list less-than:     all the elements are <  pivot
  -- lge: list greater-equal: all the elements are >= pivot
  let llt, lge :: SBV a -> SList a -> SBool
      llt = smtFunction "llt" $ \pivot l -> null l .|| let (x, xs) = uncons l in x .<  pivot .&& llt pivot xs
      lge = smtFunction "lge" $ \pivot l -> null l .|| let (x, xs) = uncons l in x .>= pivot .&& lge pivot xs

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
                                 , lltCorrect  `at` (Inst @"xs" ys, Inst @"e"  x,  Inst @"pivot" pivot)

                                   -- Use induction hypothesis to get rid of the second conjunct. We need to tell
                                   -- the prover that xs is a sublist of ys too so it can satisfy its precondition
                                 , sublistTail `at` (Inst @"x" x, Inst @"xs" xs, Inst @"ys" ys)
                                 , ih          `at` (Inst @"pivot" pivot, Inst @"ys" ys)
                                 ]
                              =: sTrue
                              =: qed

  -- Variant of the above for the permutation case
  lltPermutation <-
     calc "lltPermutation"
           (\(Forall @"xs" xs) (Forall @"pivot" pivot) (Forall @"ys" ys) -> llt pivot ys .&& isPermutation xs ys .=> llt pivot xs) $
           \xs pivot ys -> [llt pivot ys, isPermutation xs ys]
                        |- llt pivot xs
                        ?? [ lltSublist    `at` (Inst @"xs" xs, Inst @"pivot" pivot, Inst @"ys" ys)
                           , sublistIfPerm `at` (Inst @"xs" xs, Inst @"ys" ys)
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
                        ?? [ lgeSublist    `at` (Inst @"xs" xs, Inst @"pivot" pivot, Inst @"ys" ys)
                           , sublistIfPerm `at` (Inst @"xs" xs, Inst @"ys" ys)
                           ]
                        =: sTrue
                        =: qed

  --------------------------------------------------------------------------------------------
  -- Part III. Helper lemmas for partition
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
     (\(Forall @"l" l) (Forall @"pivot" pivot) -> length (fst (partition @a pivot l)) .<= length l)
     (\l (_ :: SBV a) -> length @a l) $
     \ih l pivot -> [] |- length (fst (partition @a pivot l)) .<= length l
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
                                       =: qed)

  -- The second element of partition does not increase in size
  partitionNotLongerSnd <- sInduct "partitionNotLongerSnd"
     (\(Forall @"l" l) (Forall @"pivot" pivot) -> length (snd (partition @a pivot l)) .<= length l)
     (\l (_ :: SBV a) -> length @a l) $
     \ih l pivot -> [] |- length (snd (partition @a pivot l)) .<= length l
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
                                       =: qed)

  --------------------------------------------------------------------------------------------
  -- Part IV. Helper lemmas for count
  --------------------------------------------------------------------------------------------

  -- Count is preserved over partition
  let countTuple :: SBV a -> STuple [a] [a] -> SInteger
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
  -- Part V. Prove that the output of quick sort is a permutation of its input
  --------------------------------------------------------------------------------------------

  sortCountsMatch <-
     sInduct "sortCountsMatch"
             (\(Forall @"xs" xs) (Forall @"e" (e :: SBV a)) -> count e xs .== count e (quickSort xs))
             (\xs (_ :: SBV a) -> length @a xs) $
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
                                   ?? [ ih                    `at` (Inst @"xs" lo, Inst @"e" e)
                                      , partitionNotLongerFst `at` (Inst @"l"  as, Inst @"pivot" a)
                                      ]
                                   ?? "IH on lo"
                                   =: count e lo + count e (singleton a) + count e (quickSort hi)
                                   ?? [ ih                    `at` (Inst @"xs" hi, Inst @"e" e)
                                      , partitionNotLongerSnd `at` (Inst @"l"  as, Inst @"pivot" a)
                                      ]
                                   ?? "IH on hi"
                                   =: count e lo + count e (singleton a) + count e hi
                                   ?? countPartition `at` (Inst @"xs" as, Inst @"pivot" a, Inst @"e" e)
                                   =: count e xs
                                   =: qed)

  sortIsPermutation <- lemma "sortIsPermutation" (\(Forall @"xs" xs) -> isPermutation xs (quickSort xs)) [sortCountsMatch]

  --------------------------------------------------------------------------------------------
  -- Part VI. Helper lemmas for nonDecreasing
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
  -- Part VII. Prove that the output of quick sort is non-decreasing
  --------------------------------------------------------------------------------------------
  sortIsNonDecreasing <-
     sInductWith cvc5 "sortIsNonDecreasing"
             (\(Forall @"xs" xs) -> nonDecreasing (quickSort xs))
             (length @a) $
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
                                      , ih `at` Inst @"xs" lo  -- nonDecreasing (quickSort lo)
                                      , ih `at` Inst @"xs" hi  -- nonDecreasing (quickSort hi)

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
  -- Part VIII. Putting it together
  --------------------------------------------------------------------------------------------

  qs <- lemma (atProxy p "quickSortIsCorrect")
           (\(Forall @"xs" xs) -> let out = quickSort xs in isPermutation xs out .&& nonDecreasing out)
           [sortIsPermutation, sortIsNonDecreasing]

  -- | We can display the dependencies in a proof
  liftIO $ do putStrLn "== Proof tree:"
              putStr $ showProofTree True qs

  pure qs
