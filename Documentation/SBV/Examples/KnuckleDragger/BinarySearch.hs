-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.BinarySearch
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving binary search correct
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.BinarySearch where

import Prelude hiding (null, elem, notElem, tail, length, (!!))

import Data.SBV
import Data.SBV.List
import Data.SBV.Maybe
import Data.SBV.Tools.KnuckleDragger

-- * Binary search

-- | Encode binary search in a functional style. Note that since
-- functional lists in Haskell (or SMTLib) don't have constant time
-- access to arbitrary elements, this isn't really a fast implementation.
-- The idea here is to prove the algorithm correct, not it's complexity!
bsearch :: SInteger -> SList Integer -> SMaybe Integer
bsearch target elems = bsearchLH target elems 0 (length elems - 1)

-- | Binary search with search bounds made explicit.
bsearchLH :: SInteger -> SList Integer -> SInteger -> SInteger -> SMaybe Integer
bsearchLH = smtFunction "bsearch" $ \x xs low high ->
              ite (low .> high)
                  sNothing
                  (let mid  = low + (high - low) `sEDiv` 2
                       xmid = xs !! mid
                   in ite (xmid .== x)
                          (sJust mid)
                          (ite (xmid .< x)
                               (bsearchLH x xs (mid + 1) high)
                               (bsearchLH x xs low (mid - 1))))

-- * Correctness proof

-- | A predicate testing whether a given list is non-decreasing.
nonDecreasing :: SList Integer -> SBool
nonDecreasing = smtFunction "nonDecreasing" $ \l ->  null l .|| null (tail l)
                                                 .|| let (x, l') = uncons l
                                                         (y, _)  = uncons l'
                                                     in x .<= y .&& nonDecreasing l'

-- | The proof will crucially depend on the quantity @high - low + 1@ at each recursive call.
-- So, we first rewrite the function making this quantity explicit. Note that this value
-- is not used by the function explicitly, it simply allows us to track the length of the
-- sublist of the input list that we are currently searching.
bsearchWithInv :: SInteger -> SInteger -> SList Integer -> SMaybe Integer
bsearchWithInv inv target elems = bsearchWithInvLH inv target elems 0 (length elems - 1)

-- | Binary search with invariant and search bounds made explicit.
bsearchWithInvLH :: SInteger -> SInteger -> SList Integer -> SInteger -> SInteger -> SMaybe Integer
bsearchWithInvLH = smtFunction "bsearchWithInv" $ \_inv x xs low high ->
                ite (low .> high)
                    sNothing
                    (let mid  = low + (high - low) `sEDiv` 2
                         xmid = xs !! mid
                     in ite (xmid .== x)
                            (sJust mid)
                            (ite (xmid .< x)
                                 (bsearchWithInvLH (high - mid) x xs (mid + 1) high)
                                 (bsearchWithInvLH (mid - low)  x xs low (mid - 1))))

-- | Correctness of binary search.
--
-- We have:
--
-- >>> correctness
correctness :: IO Proof
correctness = runKD $ do

  -- First establish that our two variants of binary search are equivalent:
  let bsearchI x xs = bsearchWithInv (length xs) x xs

  bsearchEq <- sInduct "bsearchEq"
                       (\(Forall @"inv" inv) (Forall @"x" x) (Forall @"xs" xs) (Forall @"low" low) (Forall @"high" high)
                             -> inv .== high - low + 1 .=> bsearchWithInvLH inv x xs low high .== bsearchLH x xs low high) $
                       \ih inv x xs low high ->
                             [inv .== high - low + 1]
                          |- bsearchWithInvLH inv x xs low high
                          =: ite (low .> high)
                                 sNothing
                                 (let mid  = low + (high - low) `sEDiv` 2
                                      xmid = xs !! mid
                                  in ite (xmid .== x)
                                         (sJust mid)
                                         (ite (xmid .< x)
                                              (bsearchWithInvLH (high - mid) x xs (mid + 1) high)
                                              (bsearchWithInvLH (mid - low)  x xs low (mid - 1))))
                          ?? [ hprf (ih `at` ( Inst @"inv" (high - (low + (high - low) `sEDiv` 2))
                                             , Inst @"x" x
                                             , Inst @"xs" xs
                                             , Inst @"low"  (low + (high - low) `sEDiv` 2 + 1)
                                             , Inst @"high" high))
                             , hyp (inv .== high - low + 1)
                             ]
                          =: ite (low .> high)
                                 sNothing
                                 (let mid  = low + (high - low) `sEDiv` 2
                                      xmid = xs !! mid
                                  in ite (xmid .== x)
                                         (sJust mid)
                                         (ite (xmid .< x)
                                              (bsearchLH                    x xs (mid + 1) high)
                                              (bsearchWithInvLH (mid - low) x xs low (mid - 1))))
                          ?? [ hprf (ih `at` ( Inst @"inv" (low + (high - low) `sEDiv` 2 - low)
                                             , Inst @"x" x
                                             , Inst @"xs" xs
                                             , Inst @"low"  low
                                             , Inst @"high" (low + (high - low) `sEDiv` 2 - 1)))
                             , hyp (inv .== high - low + 1)
                             ]
                          =: ite (low .> high)
                                 sNothing
                                 (let mid  = low + (high - low) `sEDiv` 2
                                      xmid = xs !! mid
                                  in ite (xmid .== x)
                                         (sJust mid)
                                         (ite (xmid .< x)
                                              (bsearchLH x xs (mid + 1) high)
                                              (bsearchLH x xs low (mid - 1))))
                          =: bsearchLH x xs low high
                          =: qed

  -- First prove the result when the target is in the list
  bsearchP <- lemma "bsearchPresent"
                    (\(Forall @"x" x) (Forall @"xs" xs) ->
                         nonDecreasing xs .&& x `elem` xs .=> xs !! fromJust (bsearchI x xs) .== x)
                    [sorry]

  -- Now prove the result when the target is not in the list
  bsearchA <- lemma "bsearchAbsent"
                    (\(Forall @"x" x) (Forall @"xs" xs) -> x `notElem` xs .=> isNothing (bsearchI x xs))
                    [sorry]

  -- Prove the correctness using the helpers when target is in the list and otherwise:
  bsearchICorrect <- calc "bsearchICorrect"
        (\(Forall @"x" x) (Forall @"xs" xs) ->
             nonDecreasing xs .=> let res = bsearchI x xs
                                  in ite (x `elem` xs)
                                         (xs !! fromJust res .== x)
                                         (isNothing res)) $
        \x xs -> [nonDecreasing xs]
              |- let res = bsearchI x xs
                 in ite (x `elem` xs)
                        (xs !! fromJust res .== x)
                        (isNothing res)
              =: cases [ x `elem` xs    ==> xs !! fromJust (bsearchI x xs) .== x
                                         ?? [ hyp (nonDecreasing xs)
                                            , hprf (bsearchP `at` (Inst @"x" x, Inst @"xs" xs))
                                            ]
                                         =: sTrue
                                         =: qed
                       , x `notElem` xs ==> isNothing (bsearchI x xs)
                                         ?? [ hyp (nonDecreasing xs)
                                            , hprf (bsearchA `at` (Inst @"x" x, Inst @"xs" xs))
                                            ]
                                         =: sTrue
                                         =: qed
                       ]

  -- Finally prove the same holds for bsearch itself:
  calc "bsearchCorrect"
        (\(Forall @"x" x) (Forall @"xs" xs) ->
            nonDecreasing xs .=> let res = bsearch x xs
                                 in ite (x `elem` xs)
                                        (xs !! fromJust res .== x)
                                        (isNothing res)) $
        \x xs -> [nonDecreasing xs]
              |- let res = bsearch x xs
                 in ite (x `elem` xs)
                    (xs !! fromJust res .== x)
                    (isNothing res)
              ?? [ hprf (bsearchICorrect `at` (Inst @"x" x, Inst @"xs" xs))
                 , hprf (bsearchEq       `at` ( Inst @"inv"  (length xs)
                                              , Inst @"x"    x
                                              , Inst @"xs"   xs
                                              , Inst @"low"  (0 :: SInteger)
                                              , Inst @"high" (length xs - 1)
                                              ))
                 , hyp  (nonDecreasing xs)
                 ]
              =: sTrue
              =: qed
