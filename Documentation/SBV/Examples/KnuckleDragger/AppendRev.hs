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

-- | Use an uninterpreted type for the elements
data Elt
mkUninterpretedSort ''Elt

-- | @xs ++ [] == xs@
--
-- We have:
--
-- >>> appendNull
-- Lemma: appendNull                       Q.E.D.
appendNull :: IO Proven
appendNull = lemma "appendNull"
                   (\(Forall @"xs" (xs :: SList Elt)) -> xs ++ SL.nil .== xs)
                   []

-- | @(x : xs) ++ ys == x : (xs ++ ys)@
--
-- We have:
--
-- >>> consApp
-- Lemma: consApp                          Q.E.D.
consApp :: IO Proven
consApp = lemma "consApp"
                (\(Forall @"x" (x :: SElt)) (Forall @"xs" xs) (Forall @"ys" ys) -> (x .: xs) ++ ys .== x .: (xs ++ ys))
                []

-- | @(xs ++ ys) ++ zs == xs ++ (ys ++ zs)@
--
-- We have:
--
-- >>> appendAssoc
-- Lemma: appendAssoc                      Q.E.D.
appendAssoc :: IO Proven
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
-- >>> revApp
-- Lemma: revApp                           Q.E.D.
revApp :: IO Proven
revApp = do
   let q :: SymVal a => SList a -> SList a -> SBool
       q xs ys = reverse (xs ++ ys) .== reverse ys ++ reverse xs

   lemma "revApp" (\(Forall @"xs" (xs :: SList Elt)) (Forall @"ys" ys) -> q xs ys)
         [induct2 (q @Elt)]

-- | @reverse (reverse xs) == xs@
--
-- We have:
--
-- >>> reverseReverse
-- Lemma: revApp                           Q.E.D.
-- Lemma: reverseReverse                   Q.E.D.
reverseReverse :: IO Proven
reverseReverse = do
   lRevApp <- revApp

   let p :: SymVal a => SList a -> SBool
       p xs = reverse (reverse xs) .== xs

   lemma "reverseReverse"
         (\(Forall @"xs" (xs :: SList Elt)) -> p xs)
         [induct (p @Elt), lRevApp]
