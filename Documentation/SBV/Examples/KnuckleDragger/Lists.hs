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

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-unused-do-bind #-}

module Documentation.SBV.Examples.KnuckleDragger.Lists where

import Prelude hiding (sum, length, (++))

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

import Data.SBV.List ((.:))
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
-- Axiom: List(a).induction                Admitted.
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
-- Axiom: List(a).induction                Admitted.
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

-- | Define append. Note that SBV already defines append, but we'll give our explicit recursive
-- definition here so we can reason about it explicitly.
(++) :: SymVal a => SList a -> SList a -> SList a
(++) = smtFunction "append" $ \xs ys -> ite (SL.null xs)
                                            ys
                                            (SL.head xs .: SL.tail xs ++ ys)
infixr 5 ++

-- | A helper lemma, pushing a cons into an append. This is a generator lemma, since we'll use it multiple times. We have:
--
-- >>> consApp "" (id @(SList Integer))
consApp :: SymVal a => String -> (SList a -> SList a) -> IO Proven
consApp top f = lemma (top <> (if null top then "" else ".") <> "consApp")
                   (\(Forall @"x" x) (Forall @"xs" xs) (Forall @"ys" ys) -> f ((x .: xs) ++ ys) .== f (x .: (xs ++ ys)))
                   []

-- | Prove that list append is associative.
--
-- We have:
--
-- >>> appendAssoc
-- Axiom: List(a).induction                Admitted.
-- Lemma: cons_app                         Q.E.D.
-- Lemma: appendAssoc                      Q.E.D.
appendAssoc :: String -> IO Proven
appendAssoc top = do
   -- The classic proof by induction on xs
   let p :: SymVal a => SList a -> SList a -> SList a -> SBool
       p xs ys zs = xs ++ (ys ++ zs) .== (xs ++ ys) ++ zs

   -- Do the proof over integers. We use 'inductionPrinciple3', since our predicate has 3 arguments.
   induct <- inductionPrinciple3 (p @Integer)

   -- Get access to consApp
   lConsApp <- consApp top (id @(SList Integer))

   lemma (top <> ".appendAssoc")
         (\(Forall @"xs" (xs :: SList Integer)) (Forall @"ys" ys) (Forall @"zs" zs) -> p xs ys zs)
         [lConsApp , induct]

-- | Prove that reversing a list twice leaves the list unchanged.
reverseReverse :: IO Proven
reverseReverse = do
   -- Definition of reverse
   let rev :: SymVal a => SList a -> SList a
       rev = smtFunction "rev" $ \xs -> ite (SL.null xs) SL.nil (rev (SL.tail xs) ++ SL.singleton (SL.head xs))

   let p :: SymVal a => SList a -> SBool
       p xs = rev (rev xs) .== xs

   -- Do the inductive proof
   induct <- inductionPrinciple (p @Integer)

   -- We'll also need the lemmas we proved before:
   lConsApp     <- consApp     "reverseReverse" (rev @Integer)
   lAppendAssoc <- appendAssoc "reverseReverse"
   pushCons     <- consApp     "reverseReverse" (rev @Integer)

   -- The usual inductive proof relies on @rev (xs ++ ys) == rev ys ++ rev xs@, so first prove that:
   revApp <- do
        let q :: SymVal a => SList a -> SList a -> SBool
            q xs ys = rev (xs ++ ys) .== rev ys ++ rev xs

        inductQ <- inductionPrinciple2 (q @Integer)

        sorry "revApp"
           (\(Forall @"xs" (xs :: SList Integer)) (Forall @"ys" ys) -> q xs ys)
           [inductQ, lConsApp, lAppendAssoc, pushCons]

   -- Result now follows from revApp and induction, and associativity of append.
   lemma "reverseReverse"
         (\(Forall @"xs" (xs :: SList Integer)) -> p xs)
         [induct, revApp, pushCons, lConsApp, lAppendAssoc]
