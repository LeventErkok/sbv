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
import Data.SBV.Tools.KnuckleDragger.Lists

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

-- | Count the number of occurrences of an element in a list
count :: SymVal a => SBV a -> SList a -> SInteger
count = smtFunction "count" $ \e l -> ite (null l)
                                          0
                                          (let (x, xs) = uncons l
                                               cxs     = count e xs
                                           in ite (e .== x) (1 + cxs) cxs)

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


-- | 'count' distributes over append. We have:
--
-- >>> countAppend (Proxy @Integer)
-- Inductive lemma: countAppend @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2 (unfold count)                Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4 (simplify)                    Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] countAppend @Integer
countAppend :: forall a. SymVal a => Proxy a -> IO Proof
countAppend p = runKD $
   induct (atProxy p "countAppend")
          (\(Forall @"xs" xs) (Forall @"ys" ys) (Forall @"e" (e :: SBV a)) -> count e (xs ++ ys) .== count e xs + count e ys) $
          \ih x xs ys (e :: SBV a) ->
              [] |- count e ((x .: xs) ++ ys)
                 =: count e (x .: (xs ++ ys))
                 ?? "unfold count"
                 =: (let r = count e (xs ++ ys) in ite (e .== x) (1+r) r)
                 ?? ih `at` (Inst @"ys" ys, Inst @"e" e)
                 =: (let r = count e xs + count e ys in ite (e .== x) (1+r) r)
                 ?? "simplify"
                 =: count e (x .: xs) + count e ys
                 =: qed

-- | 'count' distributes over a split list. We have:
--
-- >>> takeDropCount (Proxy @Integer)
-- Inductive lemma: countAppend @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2 (unfold count)                Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4 (simplify)                    Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: take_drop @Integer               Q.E.D.
-- Lemma: takeDropCount @Integer
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] takeDropCount @Integer
takeDropCount :: forall a. SymVal a => Proxy a -> IO Proof
takeDropCount p = runKD $ do
       capp     <- use $ countAppend p
       takeDrop <- use $ take_drop p

       calc (atProxy p "takeDropCount")
            (\(Forall @"xs" xs) (Forall @"n" n) (Forall @"e" (e :: SBV a)) -> count e (take n xs) + count e (drop n xs) .== count e xs) $
            \xs n (e :: SBV a) ->
                [] |- count e (take n xs) + count e (drop n xs)
                   ?? capp `at` (Inst @"xs" (take n xs), Inst @"ys" (drop n xs), Inst @"e" e)
                   =: count e (take n xs ++ drop n xs)
                   ?? takeDrop
                   =: count e xs
                   =: qed
