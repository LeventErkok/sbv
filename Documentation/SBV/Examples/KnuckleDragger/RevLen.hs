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
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeAbstractions    #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-unused-do-bind #-}

module Documentation.SBV.Examples.KnuckleDragger.RevLen where

import Prelude hiding (length, reverse)

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

import Data.SBV.List (reverse, length)

-- $setup
-- >>> -- For doctest purposes only:
-- >>> :set -XScopedTypeVariables
-- >>> import Control.Exception
-- >>> import Data.SBV.Tools.KnuckleDragger(runKD)

-- | Use an uninterpreted type for the elements
data Elt
mkUninterpretedSort ''Elt

-- | @length xs == length (reverse xs)@
--
-- We have:
--
-- >>> runKD revLen
-- Lemma: revLen                           Q.E.D.
revLen :: KD Proven
revLen = do
   let p :: SList Elt -> SBool
       p xs = length (reverse xs) .== length xs

   lemma "revLen"
         (\(Forall @"xs" xs) -> p xs)
         [induct p]

-- | An example where we attempt to prove a non-theorem. Notice the counter-example
-- generated for:
--
-- @length xs = ite (length xs .== 3) 5 (length xs)@
--
-- We have:
--
-- >>> runKD badRevLen `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: badRevLen
-- *** Failed to prove badRevLen.
-- Falsifiable. Counter-example:
--   xs = [Elt!val!1,Elt!val!2,Elt!val!1] :: [Elt]
badRevLen :: KD ()
badRevLen = do
   let p :: SList Elt -> SBool
       p xs = length (reverse xs) .== ite (length xs .== 3) 5 (length xs)

   lemma "badRevLen"
         (\(Forall @"xs" xs) -> p xs)
         [induct p]

   pure ()
