-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.Basics
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Some basic KD usage.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ExplicitForAll     #-}
{-# LANGUAGE TypeAbstractions   #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.Basics where

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

#ifdef DOCTEST
-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> :set -XTypeApplications
-- >>> import Data.SBV
-- >>> import Control.Exception
#endif

-- * Truth and falsity

-- | @sTrue@ is provable.
--
-- We have:
--
-- >>> trueIsProvable
-- Lemma: true                             Q.E.D.
-- [Proven] true
trueIsProvable :: IO Proof
trueIsProvable = runKD $ lemma "true" sTrue []

-- | @sFalse@ isn't provable.
--
-- We have:
--
-- >>> falseIsn'tProvable `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: sFalse
-- *** Failed to prove sFalse.
-- Falsifiable
falseIsn'tProvable :: IO ()
falseIsn'tProvable = runKD $ do
        _won'tGoThrough <- lemma "sFalse" sFalse []
        pure ()

-- * Quantification

-- | Basic quantification example: For every integer, there's a larger integer.
--
-- We have:
-- >>> largerIntegerExists
-- Lemma: largerIntegerExists              Q.E.D.
-- [Proven] largerIntegerExists
largerIntegerExists :: IO Proof
largerIntegerExists = runKD $ lemma "largerIntegerExists"
                                    (\(Forall @"x" x) (Exists @"y" y) -> x .< (y :: SInteger))
                                    []

-- * Basic connectives

-- | Pushing a universal through conjunction. We have:
--
-- >>> forallConjunction @Integer (uninterpret "p") (uninterpret "q")
-- Lemma: forallConjunction                Q.E.D.
-- [Proven] forallConjunction
forallConjunction :: forall a. SymVal a => (SBV a -> SBool) -> (SBV a -> SBool) -> IO Proof
forallConjunction p q = runKD $ do
    let qb = quantifiedBool

    lemma "forallConjunction"
           (      (qb (\(Forall @"x" x) -> p x) .&& qb (\(Forall @"x" x) -> q x))
            .<=> -----------------------------------------------------------------
                          qb (\(Forall @"x" x) -> p x .&& q x)
           )
           []

-- | Pushing an existential through disjunction. We have:
--
-- >>> existsDisjunction @Integer (uninterpret "p") (uninterpret "q")
-- Lemma: existsDisjunction                Q.E.D.
-- [Proven] existsDisjunction
existsDisjunction :: forall a. SymVal a => (SBV a -> SBool) -> (SBV a -> SBool) -> IO Proof
existsDisjunction p q = runKD $ do
    let qb = quantifiedBool

    lemma "existsDisjunction"
           (      (qb (\(Exists @"x" x) -> p x) .|| qb (\(Exists @"x" x) -> q x))
            .<=> -----------------------------------------------------------------
                          qb (\(Exists @"x" x) -> p x .|| q x)
           )
           []

-- | We cannot push a universal through a disjunction. We have:
--
-- >>> forallDisjunctionNot @Integer (uninterpret "p") (uninterpret "q") `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: forallConjunctionNot
-- *** Failed to prove forallConjunctionNot.
-- Falsifiable. Counter-example:
--   p :: Integer -> Bool
--   p 2 = True
--   p 1 = False
--   p _ = True
-- <BLANKLINE>
--   q :: Integer -> Bool
--   q 2 = False
--   q 1 = True
--   q _ = True
--
-- Note how @p@ assigns two selected values to @True@ and everything else to @False@, while @q@ does the exact opposite.
-- So, there is no common value that satisfies both, providing a counter-example. (It's not clear why the solver finds
-- a model with two distinct values, as one would have sufficed. But it is still a valud model.)
forallDisjunctionNot :: forall a. SymVal a => (SBV a -> SBool) -> (SBV a -> SBool) -> IO ()
forallDisjunctionNot p q = runKD $ do
    let qb = quantifiedBool

    -- This won't prove!
    _won'tGoThrough <- lemma "forallConjunctionNot"
                             (      (qb (\(Forall @"x" x) -> p x) .|| qb (\(Forall @"x" x) -> q x))
                              .<=> -----------------------------------------------------------------
                                              qb (\(Forall @"x" x) -> p x .|| q x)
                             )
                             []

    pure ()

-- | We cannot push an existential through conjunction. We have:
--
-- >>> existsConjunctionNot @Integer (uninterpret "p") (uninterpret "q") `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: existsConjunctionNot
-- *** Failed to prove existsConjunctionNot.
-- Falsifiable. Counter-example:
--   p :: Integer -> Bool
--   p 1 = False
--   p _ = True
-- <BLANKLINE>
--   q :: Integer -> Bool
--   q 1 = True
--   q _ = False
--
-- In this case, we again have a predicate That disagree at every point, providing a counter-example.
existsConjunctionNot :: forall a. SymVal a => (SBV a -> SBool) -> (SBV a -> SBool) -> IO ()
existsConjunctionNot p q = runKD $ do
    let qb = quantifiedBool

    _wont'GoThrough <- lemma "existsConjunctionNot"
                             (      (qb (\(Exists @"x" x) -> p x) .&& qb (\(Exists @"x" x) -> q x))
                              .<=> -----------------------------------------------------------------
                                              qb (\(Exists @"x" x) -> p x .&& q x)
                             )
                            []

    pure ()

-- * No termination checks

-- | It's important to realize that KnuckleDragger proofs in SBV neither check nor guarantee that the
-- functions we use are terminating. This is beyond the scope (and current capabilities) of what SBV can handle.
-- That is, the proof is up-to-termination, i.e., any proof implicitly assumes all functions defined (or axiomatized)
-- terminate for all possible inputs. If non-termination is possible, then the logic becomes inconsistent, i.e.,
-- we can prove arbitrary results.
--
-- Here is a simple example where we tell SBV that there is a function @f@ with non terminating behavior. Using this,
-- we can deduce @False@:
--
-- >>> noTerminationChecks
-- Axiom: bad
-- Lemma: noTerminationImpliesFalse
--   Step: 1 (bad @ (n |-> 0 :: SInteger)) Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] noTerminationImpliesFalse
noTerminationChecks :: IO Proof
noTerminationChecks = runKD $ do

   let f :: SInteger -> SInteger
       f = uninterpret "f"

   badAxiom <- axiom "bad" (\(Forall @"n" n) -> f n .== 1 + f n)

   calc "noTerminationImpliesFalse"
        sFalse
        ([] |- f 0
            ?? badAxiom `at` Inst @"n" (0 :: SInteger)
            =: 1 + f 0
            =: qed)
