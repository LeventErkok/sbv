-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.AppendRev
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Example use of the KnuckleDragger, on list append and reverses.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.AppendRev where

import Prelude hiding (reverse, (++))

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

import Data.SBV.List ((.:), (++), reverse)
import qualified Data.SBV.List as SL

#ifndef HADDOCK
-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV.Tools.KnuckleDragger(runKD)
#endif

-- | Use an uninterpreted type for the elements
data Elt
mkUninterpretedSort ''Elt

-- | @xs ++ [] == xs@
--
-- We have:
--
-- >>> runKD appendNull
-- Lemma: appendNull                       Q.E.D.
appendNull :: KD Proof
appendNull = lemma "appendNull"
                   (\(Forall @"xs" (xs :: SList Elt)) -> xs ++ SL.nil .== xs)
                   []

-- | @(x : xs) ++ ys == x : (xs ++ ys)@
--
-- We have:
--
-- >>> runKD consApp
-- Lemma: consApp                          Q.E.D.
consApp :: KD Proof
consApp = lemma "consApp"
                (\(Forall @"x" (x :: SElt)) (Forall @"xs" xs) (Forall @"ys" ys) -> (x .: xs) ++ ys .== x .: (xs ++ ys))
                []

-- | @(xs ++ ys) ++ zs == xs ++ (ys ++ zs)@
--
-- We have:
--
-- >>> runKD appendAssoc
-- Lemma: appendAssoc                      Q.E.D.
appendAssoc :: KD Proof
appendAssoc = do
   -- The classic proof by induction on xs
   let p :: SymVal a => SList a -> SList a -> SList a -> SBool
       p xs ys zs = xs ++ (ys ++ zs) .== (xs ++ ys) ++ zs

   lemma "appendAssoc"
         (\(Forall @"xs" (xs :: SList Elt)) (Forall @"ys" ys) (Forall @"zs" zs) -> p xs ys zs)
         []

-- | @reverse (xs ++ ys) == reverse ys ++ reverse xs@
-- We have:
--
-- >>> runKD revApp
-- Lemma: revApp                           Q.E.D.
revApp :: KD Proof
revApp = do
   let q :: SymVal a => SList a -> SList a -> SBool
       q xs ys = reverse (xs ++ ys) .== reverse ys ++ reverse xs

   lemma "revApp" (\(Forall @"xs" (xs :: SList Elt)) (Forall @"ys" ys) -> q xs ys)
         [induct2 (q @Elt)]

-- | @reverse (reverse xs) == xs@
--
-- We have:
--
-- >>> runKD reverseReverse
-- Lemma: revApp                           Q.E.D.
-- Lemma: reverseReverse                   Q.E.D.
reverseReverse :: KD Proof
reverseReverse = do
   lRevApp <- revApp

   let p :: SymVal a => SList a -> SBool
       p xs = reverse (reverse xs) .== xs

   lemma "reverseReverse"
         (\(Forall @"xs" (xs :: SList Elt)) -> p xs)
         [induct (p @Elt), lRevApp]
