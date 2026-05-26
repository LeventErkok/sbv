-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.RunLength
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving that run-length decoding inverts encoding. We define:
--
--   * @encode@: groups consecutive equal elements into (value, count) pairs
--   * @decode@: expands each pair back into a run of elements
--
-- and prove @decode (encode xs) == xs@ for all finite lists @xs@.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.RunLength where

import Prelude hiding (length, head, tail, null, reverse, (++), replicate, fst, snd)

import Data.SBV
import Data.SBV.List
import Data.SBV.Tuple
import Data.SBV.TP

#ifdef DOCTEST
-- $setup
-- >>> :set -XOverloadedLists
-- >>> :set -XTypeApplications
-- >>> import Data.SBV
-- >>> import Data.SBV.Tuple
-- >>> import Data.SBV.TP
#endif

-- * Definitions

-- | Run-length decode: expand each (value, count) pair into a run of that element.
--
-- >>> decode (tuple (1,3) .: tuple (2,2) .: tuple (3,1) .: []) :: SList Integer
-- [1,1,1,2,2,3] :: [SInteger]
-- >>> decode ([] :: SList (Integer, Integer))
-- [] :: [SInteger]
decode :: forall a. SymVal a => SList (a, Integer) -> SList a
decode = smtFunction "decode"
       $ \ps -> [sCase| ps of
                   []            -> []
                   (e, c) : rest -> replicate c e ++ decode rest
                |]

-- | Prepend an element to a run-length encoded list. If the head run has the
-- same value, we increment its count; otherwise we create a new singleton run.
--
-- >>> encodeCons 1 (encode [1,1,2,2]) :: SList (Integer, Integer)
-- [(1,3),(2,2)] :: [(SInteger, SInteger)]
-- >>> encodeCons 5 (encode [1,1,2,2]) :: SList (Integer, Integer)
-- [(5,1),(1,2),(2,2)] :: [(SInteger, SInteger)]
encodeCons :: forall a. SymVal a => SBV a -> SList (a, Integer) -> SList (a, Integer)
encodeCons = smtFunction "encodeCons"
           $ \x ps -> [sCase| ps of
                         []                      -> [tuple (x, 1)]
                         (e, c) : rest | x .== e -> tuple (x, c + 1) .: rest
                                       | True    -> tuple (x,     1) .: ps
                      |]

-- | Run-length encode: fold from the right, using 'encodeCons' to merge
-- each element into the growing encoding.
--
-- >>> encode [1,1,1,2,2,3] :: SList (Integer, Integer)
-- [(1,3),(2,2),(3,1)] :: [(SInteger, SInteger)]
-- >>> encode ([] :: SList Integer)
-- [] :: [(SInteger, SInteger)]
-- >>> encode [4] :: SList (Integer, Integer)
-- [(4,1)] :: [(SInteger, SInteger)]
encode :: forall a. SymVal a => SList a -> SList (a, Integer)
encode = smtFunction "encode"
       $ \xs -> [sCase| xs of
                   []       -> []
                   x : rest -> encodeCons x (encode rest)
                |]

-- * Correctness

-- | @decode (encode xs) == xs@
--
-- The proof proceeds by induction on @xs@. The key helper shows that
-- decoding after 'encodeCons' is the same as consing the element,
-- provided the head count in the encoded list is positive (which
-- 'encode' always guarantees).
--
-- >>> runTPWith cvc5 $ correctness @Integer
-- Lemma: decodeEncodeCons
--   Step: 1 (3 way case split)
--     Step: 1.1.1                         Q.E.D.
--     Step: 1.1.2                         Q.E.D.
--     Step: 1.1.3                         Q.E.D.
--     Step: 1.1.4                         Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.2.4                         Q.E.D.
--     Step: 1.3.1                         Q.E.D.
--     Step: 1.3.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: encodeHeadPos
--   Step: Base                            Q.E.D.
--   Step: 1 (3 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.3                           Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma (strong): rleCorrect
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.2.4                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Functions proven terminating: decode, encode, sbv.replicate
-- [Proven] rleCorrect :: Ɐxs ∷ [Integer] → Bool
correctness :: forall a. SymVal a => TP (Proof (Forall "xs" [a] -> SBool))
correctness = do

  -- Key helper: encodeCons followed by decode is the same as consing.
  -- The condition ensures the head count is positive so that
  -- replicate (n+1) unfolds correctly.
  helper <- calc "decodeEncodeCons"
                 (\(Forall @"x" (x :: SBV a)) (Forall @"ps" ps) ->
                      (null ps .|| snd (head ps) .>= 1)
                      .=> decode (encodeCons x ps) .== x .: decode ps) $
                 \x ps -> [null ps .|| snd (head ps) .>= 1]
                       |- decode (encodeCons x ps)
                       =: [pCase| ps of
                             []                       -> decode [tuple (x, 1)]
                                                      =: replicate 1 x ++ decode []
                                                      =: [x] ++ decode []
                                                      =: x .: decode []
                                                      =: qed
                             ((e, c) : ecs) | x .== e -> decode (tuple (x, c + 1) .: ecs)
                                                      =: replicate (c + 1) x ++ decode ecs
                                                      =: x .: replicate c x ++ decode ecs
                                                      =: x .: decode (tuple (e, c) .: ecs)
                                                      =: qed
                                            | True    -> decode (tuple (x, 1) .: ps)
                                                      ?? ecs .== ecs
                                                      =: x .: decode ps
                                                      =: qed
                          |]

  -- encode always produces a list whose head (if any) has count >= 1
  -- (This is needed as a precondition for helper above.)
  encPos <- induct "encodeHeadPos"
                   (\(Forall @"xs" (xs :: SList a)) ->
                        null (encode xs) .|| snd (head (encode xs)) .>= 1) $
                   \ih (x, xs) -> []
                               |- (null (encodeCons x (encode xs)) .|| snd (head (encodeCons x (encode xs))) .>= 1)
                               =: cases [ null (encode xs)        ==> trivial
                                        , sNot (null (encode xs)) .&& x .== fst (head (encode xs))
                                           ==> snd (head (encodeCons x (encode xs))) .>= 1
                                            =: snd (head (encode xs)) + 1 .>= 1
                                            ?? ih
                                            =: sTrue
                                            =: qed
                                        , sNot (null (encode xs)) .&& x ./= fst (head (encode xs))
                                           ==> trivial
                                        ]

  -- Main theorem: decode . encode == id
  sInduct "rleCorrect"
          (\(Forall xs) -> decode @a (encode xs) .== xs)
          (length @a, []) $
          \ih xs -> [] |- decode (encode xs)
                      =: [pCase| xs of
                            []             -> trivial
                            whole@(x : ys) -> decode (encode whole)
                                           =: decode (encodeCons x (encode ys))
                                           ?? helper `at` (Inst @"x" x, Inst @"ps" (encode ys))
                                           ?? encPos `at` Inst @"xs" ys
                                           =: x .: decode (encode ys)
                                           ?? ih `at` Inst @"xs" ys
                                           =: x .: ys
                                           =: qed
                         |]
