-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Basics
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Some basic TP usage.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Basics where

import Prelude hiding(reverse, length, elem)

import Data.SBV
import Data.SBV.List
import Data.SBV.TP

import Data.Proxy
import Control.Monad (void)

#ifdef DOCTEST
-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> :set -XTypeApplications
-- >>> import Data.SBV
-- >>> import Data.SBV.TP
-- >>> import Data.Proxy
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
trueIsProvable :: IO (Proof SBool)
trueIsProvable = runTP $ lemma "true" sTrue []

-- | @sFalse@ isn't provable.
--
-- We have:
--
-- >>> falseIsn'tProvable `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: sFalse
-- *** Failed to prove sFalse.
-- Falsifiable
falseIsn'tProvable :: IO ()
falseIsn'tProvable = runTP $ do
        _won'tGoThrough <- lemma "sFalse" sFalse []
        pure ()

-- * Quantification

-- | Basic quantification example: For every integer, there's a larger integer.
--
-- We have:
-- >>> largerIntegerExists
-- Lemma: largerIntegerExists              Q.E.D.
-- [Proven] largerIntegerExists
largerIntegerExists :: IO (Proof (Forall "x" Integer -> Exists "y" Integer -> SBool))
largerIntegerExists = runTP $ lemma "largerIntegerExists"
                                    (\(Forall x) (Exists y) -> x .< y)
                                    []

-- * Basic connectives

-- | Pushing a universal through conjunction. We have:
--
-- >>> forallConjunction @Integer (uninterpret "p") (uninterpret "q")
-- Lemma: forallConjunction                Q.E.D.
-- [Proven] forallConjunction
forallConjunction :: forall a. SymVal a => (SBV a -> SBool) -> (SBV a -> SBool) -> IO (Proof SBool)
forallConjunction p q = runTP $ do
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
existsDisjunction :: forall a. SymVal a => (SBV a -> SBool) -> (SBV a -> SBool) -> IO (Proof SBool)
existsDisjunction p q = runTP $ do
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
forallDisjunctionNot p q = runTP $ do
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
existsConjunctionNot p q = runTP $ do
    let qb = quantifiedBool

    _wont'GoThrough <- lemma "existsConjunctionNot"
                             (      (qb (\(Exists @"x" x) -> p x) .&& qb (\(Exists @"x" x) -> q x))
                              .<=> -----------------------------------------------------------------
                                              qb (\(Exists @"x" x) -> p x .&& q x)
                             )
                            []

    pure ()

-- * No termination checks

-- | It's important to realize that TP proofs in SBV neither check nor guarantee that the
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
noTerminationChecks :: IO (Proof SBool)
noTerminationChecks = runTP $ do

   let f :: SInteger -> SInteger
       f = uninterpret "f"

   badAxiom <- axiom "bad" (\(Forall @"n" n) -> f n .== 1 + f n)

   calc "noTerminationImpliesFalse"
        sFalse
        ([] |- f 0
            ?? badAxiom `at` Inst @"n" (0 :: SInteger)
            =: 1 + f 0
            =: qed)

-- * Trying to prove non-theorems

-- | An example where we attempt to prove a non-theorem. Notice the counter-example
-- generated for:
--
-- @length xs == ite (length xs .== 3) 5 (length xs)@
--
-- >>> badRevLen (Proxy @Integer) `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: badRevLen @Integer
-- *** Failed to prove badRevLen @Integer.
-- Falsifiable. Counter-example:
--   xs = [14,11,14] :: [Integer]
badRevLen :: forall a. SymVal a => Proxy a -> IO ()
badRevLen _ = runTP $
   void $ lemma "badRevLen"
                (\(Forall @"xs" (xs :: SList a)) -> length (reverse xs) .== ite (length xs .== 3) 5 (length xs))
                []

-- | It is instructive to see what kind of counter-example we get if a lemma fails to prove.
-- Below, we do a variant of the 'lengthTail, but with a bad implementation over integers,
-- and see the counter-example. Our implementation returns an incorrect answer if the given list is longer
-- than 5 elements and have 42 in it:
--
-- >>> badLengthProof `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: badLengthProof
-- *** Failed to prove badLengthProof.
-- Falsifiable. Counter-example:
--   xs   = [15,11,13,16,27,42] :: [Integer]
--   imp  =                  42 :: Integer
--   spec =                   6 :: Integer
badLengthProof :: IO ()
badLengthProof = runTP $ do
   let badLength :: SList Integer -> SInteger
       badLength xs = ite (length xs .> 5 .&& 42 `elem` xs) 42 (length xs)

   void $ lemma "badLengthProof" (\(Forall @"xs" xs) -> observe "imp" (badLength xs) .== observe "spec" (length xs)) []

-- * Caching

-- | It is not unusual that TP proofs rely on other proofs. Typically, all the helpers are used together and proven in
-- one go. It is, however, useful to be able to write these proofs as top-level entries, and reuse them multiple times
-- in several proofs. (See "Documentation/SBV/Examples/TP/PowerMod.hs" for an example.) To avoid re-proving such
-- lemmas, you can turn on proof caching. The idea behind caching is simple: If we see a lemma with the same name being
-- proven again, then we simply reuse the last result. The catch here is that lemmas are identified by their names: Hence,
-- for caching to be sound, you need to make sure all names used in your proof are unique. Otherwise you can
-- conclude wrong results!
--
-- A good trick is to pay the price and run your entire proof without caching (which is the default) once, and if it is
-- all good, turn on caching to save time in regressions. (And rerun without caching after code changes.)
--
-- To demonstrate why caching can be unsound, simply consider a proof where we first prove true, and then prove false
-- but we /trick/ TP by reusing the name. If you run this, you'll see:
--
-- >>> runTP badCaching `catch` (\(_ :: SomeException) -> pure sorry)
-- Lemma: evil                             Q.E.D.
-- Lemma: evil
-- *** Failed to prove evil.
-- Falsifiable
-- [Modulo: sorry] sorry
--
-- This is good, the proof failed since it's just not true. (Except for the confusing naming printed in the trace
-- due to our own choice.)
--
-- Let's see what happens if we turn caching on:
--
-- >>> runTPWith (tpCache z3) badCaching
-- Lemma: evil                             Q.E.D.
-- Cached: evil                            Q.E.D.
-- [Proven. Cached: evil] evil
--
-- In this case we were able to ostensibly prove False, i.e., this result is unsound. But at least SBV warned us
-- that we used a cached proof (@evil@), reminding us that using unique names is a proof of obligation for the user
-- if caching is turned on. Clearly, we failed to uniquely name our proofs in this case.
--
-- Note that a bad proof obtained this way is unsound in the way that it is misleading: That is, it will lead you
-- to believe you proved something while you actually proved something else. (More technically, you cannot take the evil
-- lemma and use it to prove arbitrary things, since it's still just the proof of truth.) In this sense it is just
-- useless as opposed to soundness, but it is alarming as one can be led astray.
--
-- (Incidentally, if you really want to be evil, you can just use 'axiom' and assert false, but that's another story.)
badCaching :: TP (Proof SBool)
badCaching = do
   _    <- lemma "evil" sTrue []

   -- Attempt to prove false, using evil:
   lemma "evil" sFalse []
