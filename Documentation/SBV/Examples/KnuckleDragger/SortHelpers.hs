-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.SortHelpers
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Various definitions and lemmas that are useful for sorting related proofs.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.SortHelpers where

import Prelude hiding (null, tail, elem, head, (++), take, drop)
import Data.Proxy

import Data.SBV
import Data.SBV.List
import Data.SBV.Tools.KnuckleDragger
import Data.SBV.Tools.KnuckleDragger.List

#ifdef DOCTEST
-- $setup
-- >>> :set -XTypeApplications
-- >>> import Data.Proxy
#endif

-- | A predicate testing whether a given list is non-decreasing.
nonDecreasing :: (Ord a, SymVal a) => SList a -> SBool
nonDecreasing = smtFunction "nonDecreasing" $ \l ->  null l .|| null (tail l)
                                                 .|| let (x, l') = uncons l
                                                         (y, _)  = uncons l'
                                                     in x .<= y .&& nonDecreasing l'

-- | Are two lists permutations of each other?
isPermutation :: SymVal a => SList a -> SList a -> SBool
isPermutation xs ys = quantifiedBool (\(Forall @"x" x) -> count x xs .== count x ys)

-- | The tail of a non-decreasing list is non-decreasing. We have:
--
-- >>> nonDecrTail (Proxy @Integer)
-- Lemma: nonDecTail                       Q.E.D.
-- [Proven] nonDecTail
nonDecrTail :: forall a. (Ord a, SymVal a) => Proxy a -> IO Proof
nonDecrTail _ = runKD $
   lemma "nonDecTail"
         (\(Forall @"x" (x :: SBV a)) (Forall @"xs" xs) -> nonDecreasing (x .: xs) .=> nonDecreasing xs)
         []

-- | If we insert an element that is less than the head of a nonDecreasing list, it remains nondecreasing. We have:
--
-- >>> nonDecrIns (Proxy @Integer)
-- Lemma: nonDecrInsert                    Q.E.D.
-- [Proven] nonDecrInsert
nonDecrIns :: forall a. (Ord a, SymVal a) => Proxy a -> IO Proof
nonDecrIns _ = runKD $
   lemma "nonDecrInsert"
         (\(Forall @"x" (x :: SBV a)) (Forall @"ys" ys) -> nonDecreasing ys .&& sNot (null ys) .&& x .<= head ys
                                                       .=> nonDecreasing (x .: ys))
         []

-- | Sublist relationship
sublist :: SymVal a => SList a -> SList a -> SBool
sublist xs ys = quantifiedBool (\(Forall @"e" e) -> count e xs .> 0 .=> count e ys .> 0)

-- | 'sublist' correctness. We have:
--
-- >>> sublistCorrect (Proxy @Integer)
-- Inductive lemma: countNonNegative @Integer
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                         Q.E.D.
--     Step: 1.1.2                         Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: countElem @Integer
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                         Q.E.D.
--     Step: 1.1.2                         Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: elemCount @Integer
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: sublistCorrect @Integer
--   Step: 1                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] sublistCorrect @Integer
sublistCorrect :: forall a. (Eq a, SymVal a) => Proxy a -> IO Proof
sublistCorrect p = runKD $ do

    cElem  <- use $ countElem p
    eCount <- use $ elemCount p

    calc (atProxy p "sublistCorrect")
         (\(Forall @"xs" xs) (Forall @"ys" ys) (Forall @"x" (x :: SBV a)) -> xs `sublist` ys .&& x `elem` xs .=> x `elem` ys) $
         \xs ys (x :: SBV a) -> [xs `sublist` ys, x `elem` xs]
                             |- x `elem` ys
                             ?? [ cElem  `at` (Inst @"xs" xs, Inst @"e" x)
                                , eCount `at` (Inst @"xs" ys, Inst @"e" x)
                                ]
                             =: sTrue
                             =: qed

-- | If one list is a sublist of another, then its head is an elem. We have:
--
-- >>> sublistElem (Proxy @Integer)
-- Inductive lemma: countNonNegative @Integer
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                         Q.E.D.
--     Step: 1.1.2                         Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: countElem @Integer
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                         Q.E.D.
--     Step: 1.1.2                         Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: elemCount @Integer
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: sublistCorrect @Integer
--   Step: 1                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: sublistElem @Integer
--   Step: 1                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] sublistElem @Integer
sublistElem :: forall a. (Eq a, SymVal a) => Proxy a -> IO Proof
sublistElem p = runKD $ do
   slc <- use $ sublistCorrect p

   calc (atProxy p "sublistElem")
        (\(Forall @"x" (x :: SBV a)) (Forall @"xs" xs) (Forall @"ys" ys) -> (x .: xs) `sublist` ys .=> x `elem` ys) $
        \(x :: SBV a) xs ys -> [(x .: xs) `sublist` ys]
                            |- x `elem` ys
                            ?? slc `at` (Inst @"xs" (x .: xs), Inst @"ys" ys, Inst @"x" x)
                            =: sTrue
                            =: qed

-- | If one list is a sublist of another so is its tail. We have:
--
-- >>> sublistTail (Proxy @Integer)
-- Lemma: sublistTail @Integer             Q.E.D.
-- [Proven] sublistTail @Integer
sublistTail :: forall a. (Eq a, SymVal a) => Proxy a -> IO Proof
sublistTail p = runKD $
  lemma (atProxy p "sublistTail")
        (\(Forall @"x" (x :: SBV a)) (Forall @"xs" xs) (Forall @"ys" ys) -> (x .: xs) `sublist` ys .=> xs `sublist` ys)
        []

-- | Permutation implies sublist. We have:
--
-- >>> permutationImpliesSublist (Proxy @Integer)
-- Lemma: permutationImpliesSublist @IntegerQ.E.D.
-- [Proven] permutationImpliesSublist @Integer
permutationImpliesSublist :: forall a. (Eq a, SymVal a) => Proxy a -> IO Proof
permutationImpliesSublist p = runKD $
  lemma (atProxy p "permutationImpliesSublist")
        (\(Forall @"xs" xs) (Forall @"ys" (ys :: SList a)) -> isPermutation xs ys .=> xs `sublist` ys)
        []
