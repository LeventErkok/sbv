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

import Prelude hiding (head, tail, null, length, (++), reverse)

import Data.SBV
import Data.SBV.List
import Data.SBV.Tuple
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

   gInduct "interleaveLen"
           (\(Forall @"xs" (xs :: SList Integer)) (Forall @"ys" ys) -> length xs + length ys .== length (interleave xs ys))
           (\(xs :: SList Integer) (ys :: SList Integer) -> length xs + length ys) $
           \ih xs (ys :: SList Integer) ->
              [] |- length xs + length ys .== length (interleave xs ys)
                 =: split xs
                          trivial
                          (\a as -> length (a .: as) + length ys .== length (interleave (a .: as) ys)
                                 =: 1 + length as + length ys .== 1 + length (interleave ys as)
                                 ?? ih `at` (Inst @"xs" ys, Inst @"ys" as)
                                 =: sTrue
                                 =: qed)

-- | Uninterleave the elements of two lists. We roughly split it into two, of alternating elements.
uninterleave :: SymVal a => SList a -> STuple [a] [a]
uninterleave lst = uninterleaveGen lst (tuple (nil, nil))

-- | Generalized form of uninterleave with the auxilary lists made explicit.C
uninterleaveGen :: SymVal a => SList a -> STuple [a] [a] -> STuple [a] [a]
uninterleaveGen = smtFunction "uninterleave" (\xs alts -> let (es, os) = untuple alts
                                                          in ite (null xs)
                                                                 (tuple (reverse es, reverse os))
                                                                 (uninterleaveGen (tail xs) (tuple (os, head xs .: es))))

{-
-- | The functions 'uninterleave' and 'interleave' are inverses so long as the inputs are of the same length.
-- We have:
--
-- >>> roundTrip
roundTrip :: IO Proof
roundTrip = runKD $ do
   -- Generalize the theorem first to take the helper lists explicitly
   roundTripGen <- lemma
         "roundTripGen"
         (\(Forall @"xs" (xs :: SList Integer)) (Forall @"ys" ys) (Forall @"alts" alts) ->
               length xs .== length ys .=> let (es, os) = untuple alts
                                           in uninterleaveGen (interleave xs ys) alts .== tuple (reverse es ++ xs, reverse os ++ ys))
         [sorry]
         {-
         (\(xs :: SList Integer) (ys :: SList Integer) (_alts :: STuple [Integer] [Integer]) -> length xs + length ys) $
         \ih (xs :: SList Integer) (ys :: SList Integer) (alts :: STuple [Integer] [Integer]) ->
             [length xs .== length ys] |- let (es, os) = untuple alts
                                          in uninterleaveGen (interleave xs ys) alts
                                          =: split xs
                                                   trivial
                                                   (\a as -> uninterleaveGen (a .: interleave ys as) alts
                                                          =: uninterleaveGen (interleave ys as) (tuple (os, a .: es))
                                                          ?? [ hprf (ih `at` (Inst @"xs" ys, Inst @"ys" as, Inst @"alts" (tuple (os, a .: es))))
                                                             , hyp  (length xs .== length ys)
                                                             ]
                                                          =: tuple (reverse es ++ xs, reverse os ++ ys)
                                                          =: qed)
                                                          -}

   -- Round-trip theorem:
   lemma "roundTrip"
         (\(Forall @"xs" (xs :: SList Integer)) (Forall @"ys" ys) ->
               length xs .== length ys .=> uninterleave (interleave xs ys) .== tuple (xs, ys)) $ [sorry, roundTripGen]
               {-
         \(xs :: SList Integer) ys ->
                [length xs .== length ys] |- uninterleave (interleave xs ys)
                                          =: uninterleaveGen (interleave xs ys) (tuple (nil, nil))
                                          ?? [ hprf (roundTripGen `at` (Inst @"xs" xs, Inst @"ys" ys, Inst @"alts" (tuple (nil :: SList Integer, nil :: SList Integer))))
                                             , hyp  (length xs .== length ys)
                                             , hprf sorry
                                             ]
                                          =: tuple (reverse nil ++ xs, reverse nil ++ ys)
                                          =: qed
                                          -}
-}