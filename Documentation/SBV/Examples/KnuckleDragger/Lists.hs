-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.Lists
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Example use of the KnuckleDragger, on lists.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeAbstractions #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-unused-do-bind #-}

module Documentation.SBV.Examples.KnuckleDragger.Lists where

import Prelude hiding (sum, length, (++))

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
-- Axiom: List(a).induction                          Admitted.
-- Lemma: length_correct                             Q.E.D.
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
-- Axiom: List(a).induction                          Admitted.
-- Lemma: bad
-- *** Failed to prove bad.
-- Falsifiable. Counter-example:
--   xs   = [42,99,100,101,59,102] :: [Integer]
--   imp  =                     42 :: Integer
--   spec =                      6 :: Integer
badProof :: IO ()
badProof = do
   let length :: SList Integer -> SInteger
       length = smtFunction "length" $ \xs -> ite (SL.length xs .> 5 .&& 42 `SL.elem` xs) 42
                                            $ ite (SL.null xs) 0 (1 + length (SL.tail xs))

       spec :: SList Integer -> SInteger
       spec = SL.length

       p :: SList Integer -> SBool
       p xs = observe "imp" (length xs) .== observe "spec" (spec xs)

   induct <- inductionPrinciple p

   lemma "bad" (\(Forall @"xs" xs) -> p xs) [induct]

   pure ()

-- | Prove that list concatenation is associative.
concatAssoc :: IO Proven
concatAssoc = do
   -- Definition of concat
   let (++) :: SList Integer -> SList Integer -> SList Integer
       (++) = smtFunction "concat" $ \xs ys -> ite (SL.null xs) ys (SL.head xs SL..: SL.tail xs ++ ys)
       infixr 5 ++

   -- The classic proof by induction on xs
   let p :: SList Integer -> SBool
       p xs = quantifiedBool $ \(Forall @"ys" ys) (Forall @"zs" zs) -> xs ++ (ys ++ zs) .== (xs ++ ys) ++ zs

   induct <- inductionPrinciple p

   chainLemma "concatAssoc" (\(Forall @"xs" xs) -> p xs)
      (\xxs ys zs -> let (_x, _xs) = SL.uncons (xxs :: SList Integer)
                     in [ SL.nil ++ (ys ++ zs)
                        , ys ++ zs
                        ]
      )
      [induct]
