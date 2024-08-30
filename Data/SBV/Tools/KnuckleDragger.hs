-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.KnuckleDragger
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A lightweight theorem proving like interface, built on top of SBV.
-- Modeled after Philip Zucker's tool with the same name, see <http://github.com/philzook58/knuckledragger>
-----------------------------------------------------------------------------

{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.KnuckleDragger (
         axiom
       , lemma,      lemmaWith
       , theorem,    theoremWith
       , chainLemma, chainLemmaWith
       , Proven
       ) where

import Data.SBV
import Control.Monad(when, void)

-- | Tag the start of an axiom or lemma. The ribbon-length is roughly
-- the width of the line you want printed. Perhaps it should be configurable,
-- but for now, this is good enough.
tag :: Int -> String -> String -> String
tag tab s w = s ++ replicate (ribbonLength - length s - tab) ' ' ++ w
  where ribbonLength :: Int
        ribbonLength = 40

-- | Tag the start of an axiom/lemma.
start :: Bool -> String -> String -> IO Int
start isVerbose knd nm = do let tab = 2 * length (filter (== '.') nm)
                            putStr $ replicate tab ' ' ++ knd ++ nm
                            when isVerbose $ putStrLn ""
                            pure tab

-- | A proven property. Note that axioms are considered proven.
data Proven = ProvenBool { boolOf :: SBool }

-- | Accept the given definition as a fact. Usually used to introduce definitial axioms,
-- giving meaning to uninterpreted symbols.
axiom :: QuantifiedBool a => String -> a -> IO Proven
axiom nm p = do putStrLn $ "Axiom: " ++ tag 0 nm "Admitted."
                pure $ ProvenBool (quantifiedBool p)

-- | Helper to generate lemma/theorem statements.
lemmaGen :: QuantifiedBool a => SMTConfig -> String -> String -> a -> [Proven] -> IO Proven
lemmaGen cfg what nm p by = do
    tab <- start (verbose cfg) what nm
    t <- isTheoremWith cfg (quantifiedBool (sAnd (map boolOf by) .=> quantifiedBool p))
    if t
       then putStrLn $ drop (length nm) $ tag tab nm "Q.E.D."
       else do putStrLn $ "\n*** Failed to prove " ++ nm ++ ":"
               print =<< proveWith cfg{verbose=True} (quantifiedBool p)
               error "Failed"
    pure $ ProvenBool (quantifiedBool p)

-- | Prove a given statement, using auxiliaries as helpers. Using the default solver.
lemma :: QuantifiedBool a => String -> a -> [Proven] -> IO Proven
lemma = lemmaGen defaultSMTCfg "Lemma: "

-- | Prove a given statement, using auxiliaries as helpers. Using the given solver.
lemmaWith :: QuantifiedBool a => SMTConfig -> String -> a -> [Proven] -> IO Proven
lemmaWith cfg = lemmaGen cfg "Lemma: "

-- | Prove a given statement, using auxiliaries as helpers. Essentially the same as 'lemma', except for the name, using the default solver.
theorem :: QuantifiedBool a => String -> a -> [Proven] -> IO Proven
theorem = lemmaGen defaultSMTCfg "Theorem: "

-- | Prove a given statement, using auxiliaries as helpers. Essentially the same as 'lemmaWith', except for the name.
theoremWith :: QuantifiedBool a => SMTConfig -> String -> a -> [Proven] -> IO Proven
theoremWith cfg = lemmaGen cfg "Theorem: "

-- | A class for doing equational reasoning style chained proofs. Use 'chainLemma' to prove a given theorem
-- as a sequence of equalities, each step following from the previous.
class ChainLemma steps step | steps -> step where

  -- | Prove a property via a series of equality steps.
  chainLemma     :: QuantifiedBool a =>              String -> a -> steps -> [Proven] -> IO Proven
  chainLemmaWith :: QuantifiedBool a => SMTConfig -> String -> a -> steps -> [Proven] -> IO Proven

  -- | Internal, shouldn't be needed outside the library
  makeSteps  :: steps -> [step]
  makeInter  :: steps -> step -> step -> SBool

  chainLemma = chainLemmaWith defaultSMTCfg

  chainLemmaWith cfg nm result steps base = do
        void (start (verbose cfg) "Chain: " (nm ++ "\n"))
        go (1 :: Int) base (makeSteps steps)
     where go _ sofar []         = lemmaWith cfg nm result sofar
           go _ sofar [_]        = lemmaWith cfg nm result sofar
           go i sofar (a:b:rest) = do let intermediate = makeInter steps a b
                                      _step <- lemmaWith cfg (nm ++ "." ++ show i) intermediate sofar
                                      go (i+1) (ProvenBool (quantifiedBool intermediate) : sofar) (b:rest)

-- | Chaining lemmas that depend on a single quantified varible.
instance (SymVal a, EqSymbolic z) => ChainLemma (SBV a -> [z]) (SBV a -> z) where
   makeSteps steps = [\x -> steps x !! i | i <- [0 .. length (steps undefined) - 1]]
   makeInter _ a b = quantifiedBool $ \(Forall x) -> a x .== b x

-- | Chaining lemmas that depend on two quantified varibles.
instance (SymVal a, SymVal b, EqSymbolic z) => ChainLemma (SBV a -> SBV b -> [z]) (SBV a -> SBV b -> z) where
   makeSteps steps = [\x y -> steps x y !! i | i <- [0 .. length (steps undefined undefined) - 1]]
   makeInter _ a b = quantifiedBool $ \(Forall x) (Forall y) -> a x y .== b x y

-- | Chaining lemmas that depend on three quantified varibles.
instance (SymVal a, SymVal b, SymVal c, EqSymbolic z) => ChainLemma (SBV a -> SBV b -> SBV c -> [z]) (SBV a -> SBV b -> SBV c -> z) where
   makeSteps steps = [\x y z -> steps x y z !! i | i <- [0 .. length (steps undefined undefined undefined) - 1]]
   makeInter _ a b = quantifiedBool $ \(Forall x) (Forall y) (Forall z) -> a x y z .== b x y z

-- | Chaining lemmas that depend on four quantified varibles.
instance (SymVal a, SymVal b, SymVal c, SymVal d, EqSymbolic z) => ChainLemma (SBV a -> SBV b -> SBV c -> SBV d -> [z]) (SBV a -> SBV b -> SBV c -> SBV d -> z) where
   makeSteps steps = [\x y z w -> steps x y z w !! i | i <- [0 .. length (steps undefined undefined undefined undefined) - 1]]
   makeInter _ a b = quantifiedBool $ \(Forall x) (Forall y) (Forall z) (Forall w) -> a x y z w .== b x y z w
