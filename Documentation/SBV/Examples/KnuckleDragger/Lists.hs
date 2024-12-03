-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.Lists
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Various KnuckleDragger proofs about lists
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeAbstractions    #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-unused-do-bind #-}

module Documentation.SBV.Examples.KnuckleDragger.Lists where

import Data.SBV
import Data.SBV.List
import Data.SBV.Tools.KnuckleDragger

import Prelude hiding(reverse, (++), any, all, notElem, filter, map)

#ifndef HADDOCK
-- $setup
-- >>> -- For doctest purposes only:
-- >>> :set -XScopedTypeVariables
-- >>> import Control.Exception
-- >>> import Data.SBV.Tools.KnuckleDragger
#endif

-- | A list of booleans is not all true, if any of them is false. We have:
--
-- >>> allAny
-- Lemma: allAny                           Q.E.D.
-- [Proven] allAny
allAny :: IO Proof
allAny = runKD $ lemma "allAny" (\(Forall @"xs" xs) -> p xs) [induct p]
  where p xs = sNot (all id xs) .== any sNot xs

-- | If an integer list doesn't have 2 as an element, then filtering for @> 2@ or @.>= 2@
-- yields the same result. We have:
--
-- >>> filterEx
-- Lemma: filterEx                         Q.E.D.
-- [Proven] filterEx
filterEx :: IO Proof
filterEx = runKD $ lemma "filterEx" (\(Forall @"xs" xs) -> p xs) [induct p]
  where p xs = (2 :: SInteger) `notElem` xs .=> (filter (.> 2) xs .== filter (.>= 2) xs)

-- | The 'filterEx' example above, except we get a counter-example if `2` can be in the list. Note that
-- we don't even need the induction tactic here. (Though having it wouldn't hurt.) We have:
--
-- >>> filterEx2 `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: filterEx
-- *** Failed to prove filterEx.
-- Falsifiable. Counter-example:
--   xs = [2] :: [Integer]
filterEx2 :: IO ()
filterEx2 = runKD $ do
        let p :: SList Integer -> SBool
            p xs = filter (.> 2) xs .== filter (.>= 2) xs

        lemma "filterEx" (\(Forall @"xs" xs) -> p xs) []

        pure ()

-- | Data declaration for an uninterpreted source type.
data A
mkUninterpretedSort ''A

-- | Data declaration for an uninterpreted target type.
data B
mkUninterpretedSort ''B

-- | An uninterpreted function, for use as a witness in the following higher-order proofs.
f :: SA -> SB
f = uninterpret "f"

-- | @reverse (x:xs) == reverse xs ++ [x]@
--
-- >>> runKD revCons
-- Lemma: revCons                          Q.E.D.
-- [Proven] revCons
revCons :: KD Proof
revCons = do
    let p :: SA -> SList A -> SBool
        p x xs = reverse (x .: xs) .== reverse xs ++ singleton x

    lemma "revCons" (\(Forall @"x" x) (Forall @"xs" xs) -> p x xs) []

-- | @map f (xs ++ ys) == map f xs ++ map f ys@
--
-- >>> runKD mapAppend
-- Lemma: mapAppend                        Q.E.D.
-- [Proven] mapAppend
mapAppend :: KD Proof
mapAppend = do
   let p :: (SA -> SB) -> SList A -> SList A -> SBool
       p g xs ys = map g (xs ++ ys) .== map g xs ++ map g ys

   lemma "mapAppend"
         (\(Forall @"xs" xs) (Forall @"ys" ys) -> p f xs ys)
         -- induction is done on the last argument, so flip to do it on xs
         [induct (flip (p f))]

-- | @map f . reverse == reverse . map f@
--
-- >>> runKD mapReverse
-- Lemma: revCons                          Q.E.D.
-- Lemma: mapAppend                        Q.E.D.
-- Chain: mapReverse
--   Lemma: mapReverse.1                   Q.E.D.
--   Lemma: mapReverse.2                   Q.E.D.
--   Lemma: mapReverse.3                   Q.E.D.
--   Lemma: mapReverse.4                   Q.E.D.
--   Lemma: mapReverse.5                   Q.E.D.
--   Lemma: mapReverse.6                   Q.E.D.
-- Lemma: mapReverse                       Q.E.D.
-- [Proven] mapReverse
mapReverse :: KD Proof
mapReverse = do
     let p :: (SA -> SB) -> SList A -> SBool
         p g xs = reverse (map g xs) .== map g (reverse xs)

     rCons <- revCons
     mApp  <- mapAppend

     chainLemma "mapReverse"
                (\(Forall @"xs" xs) -> p f xs)
                (\x xs -> [ reverse (map f (x .: xs))
                          , reverse (f x .: map f xs)
                          , reverse (map f xs) ++ singleton (f x)
                          , map f (reverse xs) ++ singleton (f x)
                          , map f (reverse xs) ++ map f (singleton x)
                          , map f (reverse xs ++ singleton x)
                          , map f (reverse (x .: xs))
                          ])
                [induct (p f), rCons, mApp]
