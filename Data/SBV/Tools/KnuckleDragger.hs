-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.KnuckleDragger
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A lightweight theorem proving like interface, built on top of SBV.
-- Inspired by and modeled after Philip Zucker's tool with the same
-- name, see <http://github.com/philzook58/knuckledragger>.
--
-- See the directory Documentation.SBV.Examples.KnuckleDragger for various examples.
-----------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE TypeAbstractions           #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.KnuckleDragger (
       -- * Propositions and their proofs
         Proposition, Proof
       -- * Adding axioms/definitions
       , axiom
       -- * Basic proofs
       , lemma,        lemmaWith
       , theorem,      theoremWith
       -- * Chain of reasoning
       , chainLemma,   chainLemmaWith
       , chainTheorem, chainTheoremWith
       -- * Induction
       , Inductive(..)
       -- * Faking proofs
       , sorry
       -- * Running KnuckleDragger proofs
       , KD, runKD, runKDWith, use
       ) where

import Data.SBV
import Data.SBV.Tools.KDKernel
import Data.SBV.Tools.KDUtils

import Control.Monad        (when)
import Control.Monad.Trans  (liftIO)
import Control.Monad.Reader (ask)

-- | Bring an IO proof into current proof context.
use :: IO Proof -> KD Proof
use = liftIO

-- | A class for doing equational reasoning style chained proofs. Use 'chainLemma' to prove a given theorem
-- as a sequence of equalities, each step following from the previous.
class ChainLemma steps step | steps -> step where

  -- | Prove a property via a series of equality steps, using the default solver.
  -- Let @H@ be a list of already established lemmas. Let @P@ be a property we wanted to prove, named @name@.
  -- Consider a call of the form @chainLemma name P [A, B, C, D] H@. Note that @H@ is
  -- a list of already proven facts, ensured by the type signature. We proceed as follows:
  --
  --    * Prove: @H -> A == B@
  --    * Prove: @H && A == B -> B == C@
  --    * Prove: @H && A == B && B == C -> C == D@
  --    * Prove: @H && A == B && B == C && C == D -> P@
  --    * If all of the above steps succeed, conclude @P@.
  --
  -- Note that if the type of steps (i.e., @A@ .. @D@ above) is 'SBool', then we use implication
  -- as opposed to equality; which better captures line of reasoning.
  --
  -- So, chain-lemma is essentially modus-ponens, applied in a sequence of stepwise equality reasoning in the case of
  -- non-boolean steps.
  --
  -- If there are no helpers given (i.e., if @H@ is empty), then this call is equivalent to 'lemmaWith'.
  -- If @H@ is a singleton, then we error-out. A single step in @H@ indicates a user-error, since there's
  -- no sequence of steps to reason about.
  chainLemma :: Proposition a => String -> a -> steps -> [Proof] -> KD Proof

  -- | Same as chainLemma, except tagged as Theorem
  chainTheorem :: Proposition a => String -> a -> steps -> [Proof] -> KD Proof

  -- | Prove a property via a series of equality steps, using the given solver.
  chainLemmaWith :: Proposition a => SMTConfig -> String -> a -> steps -> [Proof] -> KD Proof

  -- | Same as chainLemmaWith, except tagged as Theorem
  chainTheoremWith :: Proposition a => SMTConfig -> String -> a -> steps -> [Proof] -> KD Proof

  -- | Internal, shouldn't be needed outside the library
  makeSteps :: steps -> [step]
  makeInter :: steps -> step -> step -> SBool

  chainLemma nm p steps by = do cfg <- ask
                                chainLemmaWith cfg nm p steps by

  chainTheorem nm p steps by = do cfg <- ask
                                  chainTheoremWith cfg nm p steps by

  chainLemmaWith   = chainGeneric False
  chainTheoremWith = chainGeneric True

  chainGeneric :: Proposition a => Bool -> SMTConfig -> String -> a -> steps -> [Proof] -> KD Proof
  chainGeneric taggedTheorem cfg nm result steps base = do
        liftIO $ putStrLn $ "Chain: " ++ nm
        let proofSteps = makeSteps steps
            len        = length proofSteps

        when (len == 1) $
         error $ unlines $ [ "Incorrect use of chainLemma on " ++ show nm ++ ":"
                           , "**   There must be either none, or at least two steps."
                           , "**   Was given only one step."
                           ]

        go (1 :: Int) base (zipWith (makeInter steps) proofSteps (drop 1 proofSteps))

     where -- if cfg has a transcript, make sure the file is suffixed appropriately
           mkCfg i = cfg{transcript = unique <$> transcript cfg}
             where unique f = "chainLemma_" ++ show i ++ "_" ++ f

           go _ sofar []
              | taggedTheorem = theoremWith cfg nm result sofar
              | True          = lemmaWith   cfg nm result sofar
           go i sofar (p:ps)
            | True
            = do step <- lemmaGen (mkCfg i) "Lemma" ([nm, show i]) p sofar
                 go (i+1) (step : sofar) ps

-- | Chaining lemmas that depend on a single quantified variable.
instance (SymVal a, EqSymbolic z) => ChainLemma (SBV a -> [z]) (SBV a -> z) where
   makeSteps steps = [\a -> steps a !! i | i <- [0 .. length (steps undefined) - 1]]
   makeInter _ x y = quantifiedBool $ \(Forall @"a" a) -> x a .== y a

-- | Chaining lemmas that depend on two quantified variables.
instance (SymVal a, SymVal b, EqSymbolic z) => ChainLemma (SBV a -> SBV b -> [z]) (SBV a -> SBV b -> z) where
   makeSteps steps = [\a b -> steps a b !! i | i <- [0 .. length (steps undefined undefined) - 1]]
   makeInter _ x y = quantifiedBool $ \(Forall @"a" a) (Forall @"b" b) -> x a b .== y a b

-- | Chaining lemmas that depend on three quantified variables.
instance (SymVal a, SymVal b, SymVal c, EqSymbolic z) => ChainLemma (SBV a -> SBV b -> SBV c -> [z]) (SBV a -> SBV b -> SBV c -> z) where
   makeSteps steps = [\a b c -> steps a b c !! i | i <- [0 .. length (steps undefined undefined undefined) - 1]]
   makeInter _ x y = quantifiedBool $ \(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> x a b c .== y a b c

-- | Chaining lemmas that depend on four quantified variables.
instance (SymVal a, SymVal b, SymVal c, SymVal d, EqSymbolic z) => ChainLemma (SBV a -> SBV b -> SBV c -> SBV d -> [z]) (SBV a -> SBV b -> SBV c -> SBV d -> z) where
   makeSteps steps = [\a b c d -> steps a b c d !! i | i <- [0 .. length (steps undefined undefined undefined undefined) - 1]]
   makeInter _ x y = quantifiedBool $ \(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) (Forall @"d" d) -> x a b c d .== y a b c d

-- | Chaining lemmas that depend on five quantified variables.
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, EqSymbolic z) => ChainLemma (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> [z]) (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> z) where
   makeSteps steps = [\a b c d e -> steps a b c d e !! i | i <- [0 .. length (steps undefined undefined undefined undefined undefined) - 1]]
   makeInter _ x y = quantifiedBool $ \(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) (Forall @"d" d) (Forall @"e" e) -> x a b c d e .== y a b c d e

-- | Chaining lemmas that depend on a single quantified variable. Overlapping version for 'SBool' that uses implication.
instance {-# OVERLAPPING #-} SymVal a => ChainLemma (SBV a -> [SBool]) (SBV a -> SBool) where
   makeSteps steps = [\a -> steps a !! i | i <- [0 .. length (steps undefined) - 1]]
   makeInter _ x y = quantifiedBool $ \(Forall @"a" a) -> x a .=> y a

-- | Chaining lemmas that depend on two quantified variables. Overlapping version for 'SBool' that uses implication.
instance {-# OVERLAPPING #-} (SymVal a, SymVal b) => ChainLemma (SBV a -> SBV b -> [SBool]) (SBV a -> SBV b -> SBool) where
   makeSteps steps = [\a b -> steps a b !! i | i <- [0 .. length (steps undefined undefined) - 1]]
   makeInter _ x y = quantifiedBool $ \(Forall @"a" a) (Forall @"b" b) -> x a b .=> y a b

-- | Chaining lemmas that depend on three quantified variables. Overlapping version for 'SBool' that uses implication.
instance {-# OVERLAPPING #-} (SymVal a, SymVal b, SymVal c) => ChainLemma (SBV a -> SBV b -> SBV c -> [SBool]) (SBV a -> SBV b -> SBV c -> SBool) where
   makeSteps steps = [\a b c -> steps a b c !! i | i <- [0 .. length (steps undefined undefined undefined) - 1]]
   makeInter _ x y = quantifiedBool $ \(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> x a b c .=> y a b c

-- | Chaining lemmas that depend on four quantified variables. Overlapping version for 'SBool' that uses implication.
instance {-# OVERLAPPING #-} (SymVal a, SymVal b, SymVal c, SymVal d) => ChainLemma (SBV a -> SBV b -> SBV c -> SBV d -> [SBool]) (SBV a -> SBV b -> SBV c -> SBV d -> SBool) where
   makeSteps steps = [\a b c d -> steps a b c d !! i | i <- [0 .. length (steps undefined undefined undefined undefined) - 1]]
   makeInter _ x y = quantifiedBool $ \(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) (Forall @"d" d) -> x a b c d .=> y a b c d

-- | Chaining lemmas that depend on five quantified variables. Overlapping version for 'SBool' that uses implication.
instance {-# OVERLAPPING #-} (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e) => ChainLemma (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> [SBool]) (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> SBool) where
   makeSteps steps = [\a b c d e -> steps a b c d e !! i | i <- [0 .. length (steps undefined undefined undefined undefined undefined) - 1]]
   makeInter _ x y = quantifiedBool $ \(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) (Forall @"d" d) (Forall @"e" e) -> x a b c d e .=> y a b c d e
