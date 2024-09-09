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
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.AppendRev where

import Prelude hiding (sum, length, reverse, (++))

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

import Data.SBV.List ((.:), (++), reverse)
import qualified Data.SBV.List as SL

-- | @xs ++ [] == xs@
--
-- We have:
--
-- >>> appendNull
-- Lemma: appendNull                       Q.E.D.
appendNull :: IO Proven
appendNull = lemma "appendNull"
                (\(Forall @"xs" (xs :: SList Integer)) -> xs ++ SL.nil .== xs)
                []

-- | @(x : xs) ++ ys == x : (xs ++ ys)@
--
-- We have:
--
-- >>> consApp
-- Lemma: consApp                          Q.E.D.
consApp :: IO Proven
consApp = lemma "consApp"
             (\(Forall @"x" (x :: SInteger)) (Forall @"xs" xs) (Forall @"ys" ys) -> (x .: xs) ++ ys .== x .: (xs ++ ys))
             []

-- | @(xs ++ ys) ++ zs == xs ++ (ys ++ zs)@
--
-- We have:
--
-- >>> appendAssoc
-- Axiom: List(a).induction                Axiom.
-- Lemma: consApp                          Q.E.D.
-- Lemma: appendAssoc                      Q.E.D.
appendAssoc :: IO Proven
appendAssoc = do

   -- The classic proof by induction on xs
   let p :: SymVal a => SList a -> SList a -> SList a -> SBool
       p xs ys zs = xs ++ (ys ++ zs) .== (xs ++ ys) ++ zs

   -- Do the proof over integers. We use 'inductionPrinciple3', since our predicate has 3 arguments.
   induct <- inductionPrinciple3 (p @Integer)

   -- Get a hold on to the consApp lemma that we'll need
   lconsApp <- consApp

   lemma "appendAssoc"
         (\(Forall @"xs" (xs :: SList Integer)) (Forall @"ys" ys) (Forall @"zs" zs) -> p xs ys zs)
         [lconsApp , induct]

-- | @reverse (xs ++ ys) == reverse ys ++ reverse xs@
-- We have:
--
-- >>> revApp
-- Lemma: consApp                          Q.E.D.
-- Axiom: List(a).induction                Axiom.
-- Lemma: consApp                          Q.E.D.
-- Lemma: appendAssoc                      Q.E.D.
-- Chain: revApp_induction_pre
--   Lemma: revApp_induction_pre.1         Q.E.D.
--   Lemma: revApp_induction_pre.2         Q.E.D.
-- Lemma: revApp_induction_pre             Q.E.D.
-- Chain: revApp_induction_post
--   Lemma: revApp_induction_post.1        Q.E.D.
--   Lemma: revApp_induction_post.2        Q.E.D.
-- Lemma: revApp_induction_post            Q.E.D.
-- Axiom: List(a).induction                Axiom.
-- Lemma: revApp                           Q.E.D. [Modulo: sorry]
revApp :: IO Proven
revApp = do
   -- We'll need the consApp and associativity-of-append proof, so get a hold on to them
   lconsApp     <- consApp
   lAppendAssoc <- appendAssoc

   revApp_induction_pre <- chainLemma "revApp_induction_pre"
      (\(Forall @"x" (x :: SInteger)) (Forall @"xs" xs) (Forall @"ys" ys)
            -> reverse ((x .: xs) ++ ys) .== (reverse (xs ++ ys)) ++ SL.singleton x)
      (\(x :: SInteger) xs ys ->
           [ reverse ((x .: xs) ++ ys)
           , reverse (x .: (xs ++ ys))
           , reverse (xs ++ ys) ++ SL.singleton x
           ]
      ) [lconsApp]

   revApp_induction_post <- chainLemma "revApp_induction_post"
      (\(Forall @"x" (x :: SInteger)) (Forall @"xs" xs) (Forall @"ys" ys)
            -> (reverse ys ++ reverse xs) ++ SL.singleton x .== reverse ys ++ reverse (x .: xs))
      (\(x :: SInteger) xs ys ->
          [ (reverse ys ++ reverse xs) ++ SL.singleton x
          , reverse ys ++ (reverse xs ++ SL.singleton x)
          , reverse ys ++ reverse (x .: xs)
          ]
      ) [lAppendAssoc]

   let q :: SymVal a => SList a -> SList a -> SBool
       q xs ys = reverse (xs ++ ys) .== (reverse ys ++ reverse xs)

   inductQ <- inductionPrinciple2 (q @Integer)

   lemma "revApp" (\(Forall @"xs" (xs :: SList Integer)) (Forall @"ys" ys) -> reverse (xs ++ ys) .== reverse ys ++ reverse xs)
         [sorry, revApp_induction_pre, inductQ, revApp_induction_post]

-- | @reverse (reverse xs) == xs@
--
-- We have:
--
-- >>> reverseReverse
-- Axiom: List(a).induction                Axiom.
-- Lemma: consApp                          Q.E.D.
-- Lemma: appendAssoc                      Q.E.D.
-- Lemma: consApp                          Q.E.D.
-- Axiom: List(a).induction                Axiom.
-- Lemma: consApp                          Q.E.D.
-- Lemma: appendAssoc                      Q.E.D.
-- Chain: revApp_induction_pre
--   Lemma: revApp_induction_pre.1         Q.E.D.
--   Lemma: revApp_induction_pre.2         Q.E.D.
-- Lemma: revApp_induction_pre             Q.E.D.
-- Chain: revApp_induction_post
--   Lemma: revApp_induction_post.1        Q.E.D.
--   Lemma: revApp_induction_post.2        Q.E.D.
-- Lemma: revApp_induction_post            Q.E.D.
-- Axiom: List(a).induction                Axiom.
-- Lemma: revApp                           Q.E.D. [Modulo: sorry]
-- Axiom: List(a).induction                Axiom.
-- Lemma: reverseReverse                   Q.E.D. [Modulo: revApp]
reverseReverse :: IO Proven
reverseReverse = do
   lAppendAssoc <- appendAssoc
   lRevApp      <- revApp

   let p :: SymVal a => SList a -> SBool
       p xs = reverse (reverse xs) .== xs

   induct <- inductionPrinciple (p @Integer)

   lemma "reverseReverse"
         (\(Forall @"xs" (xs :: SList Integer)) -> p xs)
         [induct, lRevApp, lAppendAssoc]
