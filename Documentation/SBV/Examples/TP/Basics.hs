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
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Basics where

import Prelude hiding(reverse, length, elem)

import Data.SBV
import Data.SBV.List
import Data.SBV.TP

import Control.Monad (void)

#ifdef DOCTEST
-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> :set -XTypeApplications
-- >>> import Data.SBV
-- >>> import Data.SBV.TP
-- >>> import Control.Exception
#endif

-- * Truth and falsity

-- | @sTrue@ is provable.
--
-- We have:
--
-- >>> trueIsProvable
-- Lemma: true                             Q.E.D.
-- [Proven] true :: Bool
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
-- [Proven] largerIntegerExists :: Ɐx ∷ Integer → ∃y ∷ Integer → Bool
largerIntegerExists :: IO (Proof (Forall "x" Integer -> Exists "y" Integer -> SBool))
largerIntegerExists = runTP $ lemma "largerIntegerExists"
                                    (\(Forall x) (Exists y) -> x .< y)
                                    []

-- * Basic connectives

-- | Pushing a universal through conjunction. We have:
--
-- >>> forallConjunction @Integer (uninterpret "p") (uninterpret "q")
-- Lemma: forallConjunction                Q.E.D.
-- [Proven] forallConjunction :: Bool
forallConjunction :: forall a. SymVal a => (SBV a -> SBool) -> (SBV a -> SBool) -> IO (Proof SBool)
forallConjunction p q = runTP $ do
    let qb = quantifiedBool

    lemma "forallConjunction"
           (      (qb (\(Forall x) -> p x) .&& qb (\(Forall x) -> q x))
            .<=> -------------------------------------------------------
                          qb (\(Forall x) -> p x .&& q x)
           )
           []

-- | Pushing an existential through disjunction. We have:
--
-- >>> existsDisjunction @Integer (uninterpret "p") (uninterpret "q")
-- Lemma: existsDisjunction                Q.E.D.
-- [Proven] existsDisjunction :: Bool
existsDisjunction :: forall a. SymVal a => (SBV a -> SBool) -> (SBV a -> SBool) -> IO (Proof SBool)
existsDisjunction p q = runTP $ do
    let qb = quantifiedBool

    lemma "existsDisjunction"
           (      (qb (\(Exists x) -> p x) .|| qb (\(Exists x) -> q x))
            .<=> -------------------------------------------------------
                          qb (\(Exists x) -> p x .|| q x)
           )
           []

-- | We cannot push a universal through a disjunction. We have:
--
-- >>> forallDisjunctionNot @Integer (uninterpret "p") (uninterpret "q") `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: forallConjunctionNot
-- *** Failed to prove forallConjunctionNot.
-- Falsifiable. Counter-example:
--   p :: Integer -> Bool
--   p 4 = True
--   p 3 = False
--   p _ = True
-- <BLANKLINE>
--   q :: Integer -> Bool
--   q 4 = False
--   q 3 = True
--   q _ = True
--
-- Note how @p@ and @q@ differ in their treatment of the inputs 3 and 4, but agree everywhere else. So, for each
-- input, at least one of @p@ or @q@ is @True@, making the disjunction @True@ for all inputs. But the predicates
-- @p@ and @q@ are not universally true themselves, constituting a counter-example.
forallDisjunctionNot :: forall a. SymVal a => (SBV a -> SBool) -> (SBV a -> SBool) -> IO ()
forallDisjunctionNot p q = runTP $ do
    let qb = quantifiedBool

    -- This won't prove!
    _won'tGoThrough <- lemma "forallConjunctionNot"
                             (      (qb (\(Forall x) -> p x) .|| qb (\(Forall x) -> q x))
                              .<=> -------------------------------------------------------
                                              qb (\(Forall x) -> p x .|| q x)
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
--   p 3 = False
--   p _ = True
-- <BLANKLINE>
--   q :: Integer -> Bool
--   q 3 = True
--   q _ = False
--
-- In this case, both @p@ and @q@ have a satisfying input (for @p@ everything but 3, for @q@, only 3), but
-- there is no single value that satisfies both, thus giving us our counter-example.
existsConjunctionNot :: forall a. SymVal a => (SBV a -> SBool) -> (SBV a -> SBool) -> IO ()
existsConjunctionNot p q = runTP $ do
    let qb = quantifiedBool

    _wont'GoThrough <- lemma "existsConjunctionNot"
                             (      (qb (\(Exists x) -> p x) .&& qb (\(Exists x) -> q x))
                              .<=> -------------------------------------------------------
                                              qb (\(Exists x) -> p x .&& q x)
                             )
                            []

    pure ()

-- * QuickCheck

-- | Using quick-check as a step. This can come in handy if a proof step isn't converging,
-- or if you want to quickly see if there are any obvious counterexamples. This example prints:
--
-- @
-- Lemma: qcExample
--   Step: 1 (passed 1000 tests)           Q.E.D. [Modulo: quickCheck]
--   Step: 2 (Failed during quickTest)
-- 
-- *** QuickCheck failed for qcExample.2
-- *** Failed! Assertion failed (after 1 test):
--   n   = 175 :: Word8
--   lhs =  94 :: Word8
--   rhs =  95 :: Word8
--   val =  94 :: Word8
--
-- *** Exception: Failed
-- @
--
-- Of course, the counterexample you get might differ depending on the quickcheck outcome.
qcExample :: TP (Proof (Forall "n" Word8 -> SBool))
qcExample = calc "qcExample"
                 (\(Forall n) -> n + n .== 2 * n) $
                 \n -> [] |- n + n
                          ?? qc 1000
                          =: 2 * n
                          ?? qc 1000
                          ?? disp "val" (2 * n)
                          =: 2 * n + 1
                          =: qed

-- | We can't really prove Fermat's last theorem. But we can quick-check instances of it.
--
-- >>> runTP (qcFermat 3)
-- Lemma: qcFermat 3
--   Step: 1 (qc: Running 1000 tests)      QC OK
--   Result:                               Q.E.D. [Modulo: quickCheck]
-- [Modulo: quickCheck] qcFermat 3 :: Ɐx ∷ Integer → Ɐy ∷ Integer → Ɐz ∷ Integer → Bool
qcFermat :: Integer -> TP (Proof (Forall "x" Integer -> Forall "y" Integer -> Forall "z" Integer -> SBool))
qcFermat e = calc ("qcFermat " <> show e)
                  (\(Forall x) (Forall y) (Forall z) -> n .> 2 .=> x.^n + y.^n ./= z.^n) $
                  \x y z -> [n .> 2]
                         |- x .^ n + y .^ n ./= z .^ n
                         ?? qc 1000
                         =: sTrue
                         =: qed
  where n = literal e

-- * Termination checking

-- | When a recursive function is defined via 'smtFunction', SBV automatically checks that it terminates
-- by guessing and verifying a termination measure. Here we define a simple recursive @sumToN@ and prove
-- a property about it. Note the @Functions proven terminating@ line in the output, confirming that SBV
-- verified the termination of @sumToN@ before proceeding with the proof.
--
-- >>> terminationDemo
-- Lemma: sumToN_at_5                      Q.E.D.
-- Functions proven terminating: sumToN
-- [Proven] sumToN_at_5 :: Ɐn ∷ Integer → Bool
terminationDemo :: IO (Proof (Forall "n" Integer -> SBool))
terminationDemo = runTP $ do
    let sumToN :: SInteger -> SInteger
        sumToN = smtFunction "sumToN" $ \x -> [sCase| x of
                                                 _ | x .<= 0 -> 0
                                                 _           -> x + sumToN (x - 1)
                                              |]

    lemma "sumToN_at_5"
          (\(Forall n) -> n .== 5 .=> sumToN n .== 15)
          []

-- | If SBV cannot determine a termination measure, it will report an error. Here, we define
-- a function that recurses without decreasing any argument, and SBV rightfully rejects it:
--
-- >>> badTermination `catch` (\(e :: SomeException) -> mapM_ putStrLn . filter (\l -> take 3 l == "***") . lines $ show e)
-- *** Data.SBV: Cannot determine a termination measure.
-- ***
-- ***   Function: bad :: SBV Integer -> SBV Integer
-- ***
-- ***   Measures tried:
-- ***     abs arg1
-- ***     smax 0 arg1
-- ***     abs arg1 + smax 0 arg1
-- ***     (abs arg1, smax 0 arg1)
-- ***     (smax 0 arg1, abs arg1)
-- ***
-- *** Please use 'smtFunctionWithMeasure' to provide an explicit measure.
badTermination :: IO ()
badTermination = do
    let bad :: SInteger -> SInteger
        bad = smtFunction "bad" $ \x -> [sCase| x of
                                           _ | x .== 0 -> 0
                                           _           -> bad x
                                        |]
    r <- prove $ \x -> bad x .== bad x
    print r

-- | If the user provides an explicit but incorrect termination measure via 'smtFunctionWithMeasure',
-- SBV will detect this and report an error. Here, we use @const 0@ as a measure, which clearly
-- does not decrease at recursive calls:
--
-- >>> badMeasure `catch` (\(e :: SomeException) -> mapM_ putStrLn . filter (\l -> take 3 l == "***") . lines $ show e)
-- *** Data.SBV: Termination measure does not strictly decrease at a recursive call site.
-- ***
-- ***   Function: badM :: SBV Integer -> SBV Integer
-- ***
-- ***   Falsifiable. Counter-example:
-- ***     arg    = 1 :: Integer
-- ***     before = 0 :: Integer
-- ***     then   = 0 :: Integer
-- ***
-- *** The measure must strictly decrease at every recursive call.
badMeasure :: IO ()
badMeasure = do
    let badM :: SInteger -> SInteger
        badM = smtFunctionWithMeasure "badM" (const (0 :: SInteger), [])
             $ \x -> [sCase| x of
                        _ | x .<= 0 -> 0
                        _           -> x + badM (x - 1)
                     |]
    r <- prove $ \x -> badM x .== badM x
    print r

-- * Axioms and consistency

-- | SBV checks that recursive functions defined via 'smtFunction' terminate, verifying a termination measure, which
-- can be auto-guessed or specified by the user. However, axioms are taken on faith: they are not checked for consistency.
-- If an axiom introduces a non-terminating or contradictory definition, the logic becomes inconsistent, i.e.,
-- we can prove arbitrary results.
--
-- Here is a simple example where we assert an axiom equivalent to a non-terminating definition @f n == 1 + f n@.
-- Using this, we can deduce @False@:
--
-- >>> axiomsAreDangerous
-- Axiom: bad
-- Lemma: axiomsCanBeInconsistent
--   Step: 1 (bad @ (n |-> 0 :: SInteger)) Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] axiomsCanBeInconsistent :: Bool
axiomsAreDangerous :: IO (Proof SBool)
axiomsAreDangerous = runTP $ do

   let f :: SInteger -> SInteger
       f = uninterpret "f"

   badAxiom <- axiom "bad" (\(Forall n) -> f n .== 1 + f n)

   calc "axiomsCanBeInconsistent"
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
-- >>> badRevLen `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: badRevLen
-- *** Failed to prove badRevLen.
-- Falsifiable. Counter-example:
--   xs = [17,17,17] :: [Integer]
badRevLen :: IO ()
badRevLen = runTP $
   void $ lemma "badRevLen"
                (\(Forall @"xs" (xs :: SList Integer)) -> length (reverse xs) .== ite (length xs .== 3) 5 (length xs))
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
--   xs   = [12,15,19,25,32,42] :: [Integer]
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
-- lemmas, SBV caches proof results keyed by symbolic fingerprint. Use 'recall' to invoke a proof action that
-- benefits from the cache: if the proposition has already been proved, the cached result is returned immediately.
-- Note that 'lemma', 'calc', and 'induct' always prove from scratch and then store the result in the cache;
-- only 'recall' performs a cache lookup.
--
-- Lemma names do not need to be unique. If you prove the same proposition under different names, 'recall' will
-- show the aliases. If you prove different propositions under the same name, each is proved independently.
-- To demonstrate, note that reusing the name @"evil"@ does not cause any confusion: the second call to
-- 'lemma' proves from scratch and correctly fails:
--
-- >>> runTP duplicateNames `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: evil                             Q.E.D.
-- Lemma: evil
-- *** Failed to prove evil.
-- Falsifiable
--
-- (Incidentally, if you really want to be evil, you can just use 'axiom' and assert false, but that's another story.)
duplicateNames :: TP ()
duplicateNames = do
   -- Prove true
   _ <- lemma "evil" sTrue []

   -- Attempt to prove false, reusing the same name. Will be caught!
   _ <- lemma "evil" sFalse []

   pure ()
