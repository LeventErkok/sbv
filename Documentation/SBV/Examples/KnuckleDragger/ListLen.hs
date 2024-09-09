-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.ListLen
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Example use of the KnuckleDragger, about lenghts of lists
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-unused-do-bind #-}

module Documentation.SBV.Examples.KnuckleDragger.ListLen where

import Prelude hiding (sum, length, reverse, (++))

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

import qualified Data.SBV.List as SL

-- $setup
-- >>> -- For doctest purposes only:
-- >>> :set -XScopedTypeVariables
-- >>> import Control.Exception

-- | Prove that the length of a list is one more than the length of its tail.
--
-- We have:
--
-- >>> listLengthProof
-- Lemma: length_correct                   Q.E.D.
listLengthProof :: IO Proven
listLengthProof = do
   let length :: SList Integer -> SInteger
       length = smtFunction "length" $ \xs -> ite (SL.null xs) 0 (1 + length (SL.tail xs))

       spec :: SList Integer -> SInteger
       spec = SL.length

       p :: SList Integer -> SBool
       p xs = observe "imp" (length xs) .== observe "spec" (spec xs)

   induct <- inductionPrinciple p

   lemma "length_correct" (\(Forall @"xs" xs) -> p xs) [induct]

-- | It is instructive to see what kind of counter-example we get if a lemma fails to prove.
-- Below, we do a variant of the 'listLengthProof', but with a bad implementation, and see the
-- counter-example. Our implementation returns an incorrect answer if the given list is longer
-- than 5 elements and have 42 in it. We have:
--
-- >>> badProof `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: bad
-- *** Failed to prove bad.
-- Falsifiable. Counter-example:
--   xs   = [8,25,26,27,28,42] :: [Integer]
--   imp  =                 42 :: Integer
--   spec =                  6 :: Integer
badProof :: IO ()
badProof = do
   let length :: SList Integer -> SInteger
       length = smtFunction "length" $ \xs -> ite (SL.null xs) 0 (1 + length (SL.tail xs))

       badLength :: SList Integer -> SInteger
       badLength xs = ite (SL.length xs .> 5 .&& 42 `SL.elem` xs) 42 (length xs)

       spec :: SList Integer -> SInteger
       spec = SL.length

       p :: SList Integer -> SBool
       p xs = observe "imp" (badLength xs) .== observe "spec" (spec xs)

   induct <- inductionPrinciple p

   lemma "bad" (\(Forall @"xs" xs) -> p xs) [induct]

   pure ()
