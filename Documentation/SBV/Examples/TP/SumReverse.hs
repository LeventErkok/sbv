-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.SumReverse
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proves @sum (reverse xs) == sum xs@.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE OverloadedLists     #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.SumReverse where

import Prelude hiding ((++), foldr, sum, reverse)

import Data.SBV
import Data.SBV.TP
import Data.SBV.List


#ifdef DOCTEST
-- $setup
-- >>> :set -XFlexibleContexts
-- >>> :set -XTypeApplications
#endif

-- | @sum (reverse xs) = sum xs@
--
-- >>> revSum @Integer
-- Inductive lemma: sumAppend
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4 (associativity)               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: sumReverse
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4 (commutativity)               Q.E.D.
--   Step: 5                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] sumReverse :: Ɐxs ∷ [Integer] → Bool
revSum :: forall a. (SymVal a, Num (SBV a)) => IO (Proof (Forall "xs" [a] -> SBool))
revSum = runTP $ do

  -- helper: sum distributes over append.
  sumAppend <- induct "sumAppend"
                      (\(Forall xs) (Forall ys) -> sum (xs ++ ys) .== sum xs + sum ys) $
                      \ih (x, xs) ys -> [] |- sum ((x .: xs) ++ ys)
                                           =: sum (x .: (xs ++ ys))
                                           =: x + sum (xs ++ ys)
                                           ?? ih
                                           =: x + (sum xs + sum ys)
                                           ?? "associativity"
                                           =: (x + sum xs) + sum ys
                                           =: sum (x .: xs) + sum ys
                                           =: qed

  -- Now prove the original theorem by induction
  induct "sumReverse"
         (\(Forall xs) -> sum (reverse xs) .== sum xs) $
         \ih (x, xs) -> [] |- sum (reverse (x .: xs))
                           =: sum (reverse xs ++ [x])
                           ?? sumAppend `at` (Inst @"xs" (reverse xs), Inst @"ys" [x])
                           =: sum (reverse xs) + sum [x]
                           ?? ih
                           =: sum xs + x
                           ?? "commutativity"
                           =: x + sum xs
                           =: sum (x .: xs)
                           =: qed
