-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.GeneralizedInduction
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Examples of genralized induction
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.GeneralizedInduction where

import Prelude hiding (head, tail, null, length)

import Data.SBV
import Data.SBV.List
import Data.SBV.Tools.KnuckleDragger

#ifndef HADDOCK
-- $setup
-- >>> -- For doctest purposes only:
#endif

-- | Interleave the elements of two lists. If one ends, we take the rest from the other.
interleave :: SymVal a => SList a -> SList a -> SList a
interleave = smtFunction "interleave" (\xs ys -> ite (null  xs) ys (head xs .: interleave ys (tail xs)))

-- | Prove that interleave preserves total length.
--
-- The induction here is on the total length of the lists, and hence
-- we use the generalized induction principle. We have:
--
-- >>> interleaveLen
-- Inductive lemma (generalized): interleaveLen
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way full case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] interleaveLen
interleaveLen :: IO Proof
interleaveLen = runKD $ do

   -- The induction is on the total length of xs and ys
   let measure :: SList Integer -> SList Integer -> SInteger
       measure xs ys = length xs + length ys

   gInduct "interleaveLen"
           (\(Forall @"xs" (xs :: SList Integer)) (Forall @"ys" ys) -> length xs + length ys .== length (interleave xs ys)) measure  $
           \ih xs (ys :: SList Integer) ->
              [] |- length xs + length ys .== length (interleave xs ys)
                 =: split xs
                          trivial
                          (\a as -> length (a .: as) + length ys .== length (interleave (a .: as) ys)
                                 =: 1 + length as + length ys .== 1 + length (interleave ys as)
                                 ?? ih `at` (Inst @"xs" ys, Inst @"ys" as)
                                 =: sTrue
                                 =: qed)
