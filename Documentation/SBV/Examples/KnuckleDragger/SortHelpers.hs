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

import Prelude hiding (null, tail, elem, head)
import Data.Proxy

import Data.SBV
import Data.SBV.List
import Data.SBV.Tools.KnuckleDragger

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
