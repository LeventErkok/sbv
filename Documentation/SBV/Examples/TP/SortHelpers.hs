-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.SortHelpers
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

module Documentation.SBV.Examples.TP.SortHelpers where

import Prelude hiding (null, tail, elem, head, (++), take, drop)
import Data.Proxy

import Data.SBV
import Data.SBV.List
import Data.SBV.TP
import Data.SBV.TP.List

#ifdef DOCTEST
-- $setup
-- >>> :set -XTypeApplications
-- >>> import Data.Proxy
-- >>> import Data.SBV.TP
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
-- >>> runTP $ nonDecrTail (Proxy @Integer)
-- Lemma: nonDecrTail                      Q.E.D.
-- [Proven] nonDecrTail
nonDecrTail :: forall a. (Ord a, SymVal a) => Proxy a -> TP (Proof (Forall "x" a -> Forall "xs" [a] -> SBool))
nonDecrTail _ =
   lemma "nonDecrTail"
         (\(Forall x) (Forall xs) -> nonDecreasing (x .: xs) .=> nonDecreasing xs)
         []

-- | If we insert an element that is less than the head of a nonDecreasing list, it remains nondecreasing. We have:
--
-- >>> runTP $ nonDecrIns (Proxy @Integer)
-- Lemma: nonDecrInsert                    Q.E.D.
-- [Proven] nonDecrInsert
nonDecrIns :: forall a. (Ord a, SymVal a) => Proxy a -> TP (Proof (Forall "x" a -> Forall "xs" [a] -> SBool))
nonDecrIns _ =
   lemma "nonDecrInsert"
         (\(Forall x) (Forall xs) -> nonDecreasing xs .&& sNot (null xs) .&& x .<= head xs .=> nonDecreasing (x .: xs))
         []

-- | Sublist relationship
sublist :: SymVal a => SList a -> SList a -> SBool
sublist xs ys = quantifiedBool (\(Forall @"e" e) -> count e xs .> 0 .=> count e ys .> 0)

-- | 'sublist' correctness. We have:
--
-- >>> runTP $ sublistCorrect (Proxy @Integer)
-- Inductive lemma: countNonNeg @Integer
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
sublistCorrect :: forall a. (Eq a, SymVal a) => Proxy a -> TP (Proof (Forall "xs" [a] -> Forall "ys" [a] -> Forall "x" a -> SBool))
sublistCorrect p = do

    cElem  <- countElem p
    eCount <- elemCount p

    calc (atProxy p "sublistCorrect")
         (\(Forall xs) (Forall ys) (Forall x) -> xs `sublist` ys .&& x `elem` xs .=> x `elem` ys) $
         \(xs, ys, x) -> [xs `sublist` ys, x `elem` xs]
                      |- x `elem` ys
                      ?? cElem  `at` (Inst @"xs" xs, Inst @"e" x)
                      ?? eCount `at` (Inst @"xs" ys, Inst @"e" x)
                      =: sTrue
                      =: qed

-- | If one list is a sublist of another, then its head is an elem. We have:
--
-- >>> runTP $ sublistElem (Proxy @Integer)
-- Inductive lemma: countNonNeg @Integer
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
sublistElem :: forall a. (Eq a, SymVal a) => Proxy a -> TP (Proof (Forall "x" a -> Forall "xs" [a] -> Forall "ys" [a] -> SBool))
sublistElem p = do
   slc <- sublistCorrect p

   calc (atProxy p "sublistElem")
        (\(Forall x) (Forall xs) (Forall ys) -> (x .: xs) `sublist` ys .=> x `elem` ys) $
        \(x, xs, ys) -> [(x .: xs) `sublist` ys]
                     |- x `elem` ys
                     ?? slc `at` (Inst @"xs" (x .: xs), Inst @"ys" ys, Inst @"x" x)
                     =: sTrue
                     =: qed

-- | If one list is a sublist of another so is its tail. We have:
--
-- >>> runTP $ sublistTail (Proxy @Integer)
-- Lemma: sublistTail @Integer             Q.E.D.
-- [Proven] sublistTail @Integer
sublistTail :: forall a. (Eq a, SymVal a) => Proxy a -> TP (Proof (Forall "x" a -> Forall "xs" [a] -> Forall "ys" [a] -> SBool))
sublistTail p =
  lemma (atProxy p "sublistTail")
        (\(Forall x) (Forall xs) (Forall ys) -> (x .: xs) `sublist` ys .=> xs `sublist` ys)
        []

-- | Permutation implies sublist. We have:
--
-- >>> runTP $ sublistIfPerm (Proxy @Integer)
-- Lemma: sublistIfPerm @Integer           Q.E.D.
-- [Proven] sublistIfPerm @Integer
sublistIfPerm :: forall a. (Eq a, SymVal a) => Proxy a -> TP (Proof (Forall "xs" [a] -> Forall "ys" [a] -> SBool))
sublistIfPerm p =
  lemma (atProxy p "sublistIfPerm")
        (\(Forall xs) (Forall ys) -> isPermutation xs ys .=> xs `sublist` ys)
        []
