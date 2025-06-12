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
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE OverloadedLists     #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.SumReverse where

import Prelude hiding ((++), foldr, sum, reverse)

import Data.SBV
import Data.SBV.TP
import Data.SBV.List

import Data.Proxy

#ifdef DOCTEST
-- $setup
-- >>> :set -XFlexibleContexts
-- >>> :set -XTypeApplications
-- >>> import Data.Proxy
#endif

-- | @sum (reverse xs) = sum xs@
--
-- >>> revSum (Proxy @Integer)
-- Inductive lemma: sumAppend @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: sumReverse @Integer
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] sumReverse @Integer
revSum :: forall a. (SymVal a, Num (SBV a)) => Proxy a -> IO Proof
revSum p = runTP $ do

  -- helper: sum distributes over append.
  sumAppend <-
     induct (atProxy p "sumAppend")
            (\(Forall @"xs" xs) (Forall @"ys" ys) -> sum @a (xs ++ ys) .== sum xs + sum ys) $
            \ih x xs ys -> [] |- sum @a ((x .: xs) ++ ys)
                              =: sum (x .: (xs ++ ys))
                              =: x + sum (xs ++ ys)
                              ?? ih
                              =: x + sum xs + sum ys
                              =: sum (x .: xs) + sum ys
                              =: qed

  -- Now prove the original theorem by induction
  induct (atProxy p "sumReverse")
         (\(Forall @"xs" xs) -> sum @a (reverse xs) .== sum xs) $
         \ih x xs -> [] |- sum @a (reverse (x .: xs))
                        =: sum (reverse xs ++ [x])
                        ?? sumAppend
                        =: sum (reverse xs) + sum [x]
                        ?? ih
                        =: sum xs + x
                        =: sum (x .: xs)
                        =: qed
