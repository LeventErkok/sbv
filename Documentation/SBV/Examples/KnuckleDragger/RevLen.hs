-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.RevLen
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proof that reversing a list does not change its length.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.RevLen where

import Prelude hiding (length, reverse)

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

import Data.SBV.List (reverse, length)

-- | @length xs == length (reverse xs)@
--
-- We have:
--
-- >>> revLen
-- Lemma: revLen                           Q.E.D.
revLen :: IO Proven
revLen = do
   let p :: SList Integer -> SBool
       p xs = length (reverse xs) .== length xs

   induct <- inductionPrinciple p

   lemma "revLen"
         (\(Forall @"xs" xs) -> p xs)
         [induct]
