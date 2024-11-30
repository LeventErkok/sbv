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
{-# LANGUAGE TypeAbstractions    #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-unused-do-bind #-}

module Documentation.SBV.Examples.KnuckleDragger.Lists where

import Data.SBV
import qualified Data.SBV.List as L
import Data.SBV.Tools.KnuckleDragger

#ifndef HADDOCK
-- $setup
-- >>> -- For doctest purposes only:
-- >>> :set -XScopedTypeVariables
-- >>> import Control.Exception
#endif

-- | A list of booleans is not all true, if any of them is false. We have:
--
-- >>> allAny
-- Lemma: allAny                           Q.E.D.
-- [Proven] allAny
allAny :: IO Proof
allAny = runKD $ lemma "allAny" (\(Forall @"xs" xs) -> p xs) [induct p]
  where p xs = sNot (L.all id xs) .== L.any sNot xs

-- | If an integer list doesn't have 2 as an element, then filtering for @> 2@ or @.>= 2@
-- yields the same result. We have:
--
-- >>> filterEx
-- Lemma: filterEx                         Q.E.D.
-- [Proven] filterEx
filterEx :: IO Proof
filterEx = runKD $ lemma "filterEx" (\(Forall @"xs" xs) -> p xs) [induct p]
  where p xs = (2 :: SInteger) `L.notElem` xs .=> (L.filter (.> 2) xs .== L.filter (.>= 2) xs)

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
            p xs = L.filter (.> 2) xs .== L.filter (.>= 2) xs

        lemma "filterEx" (\(Forall @"xs" xs) -> p xs) []

        pure ()
