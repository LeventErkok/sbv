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

{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.KnuckleDragger (
         axiom
       , sorry
       , lemma,      lemmaWith
       , theorem,    theoremWith
       , chainLemma, chainLemmaWith
       , Proven
       ) where

import Data.SBV
-- import Data.SBV.SMT.SMT   (showSMTResult)
import Data.SBV.Core.Data (Constraint)

import Control.Monad(when, void)

-- | Capture the context of what we can prove via KnuckleDragger
type Proposition a = ( QuantifiedBool a
                     , QNot a
                     , Satisfiable (SkolemsTo (NegatesTo a))
                     , Constraint Symbolic (SkolemsTo (NegatesTo a))
                     , Skolemize (NegatesTo a)
                     )

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
axiom :: Proposition a => String -> a -> IO Proven
axiom nm p = do putStrLn $ "Axiom: " ++ tag 0 nm "Admitted."
                pure $ ProvenBool (quantifiedBool p)

-- | Blindly believe a proposition as a theorem. This is in essence the same as 'axiom', except
-- it serves for documentation purposes that it should be provable. It's useful during development,
-- and also when you hit a theorem that the underlying solver just can't handle.
-- giving meaning to uninterpreted symbols. The list argument is unused, but it makes the
-- signature similar to 'lemma', allowing replacing `lemma` and `sorry` easily during development process.
sorry :: Proposition a => String -> a -> [b] -> IO Proven
sorry nm p _bu = do putStrLn $ "Sorry: " ++ tag 0 nm "Blindly believed."
                    pure $ ProvenBool (quantifiedBool p)

-- | Helper to generate lemma/theorem statements.
lemmaGen :: Proposition a => SMTConfig -> String -> String -> a -> [Proven] -> IO Proven
lemmaGen cfg what nm p by = do
    tab <- start (verbose cfg) what nm

    let proposition = quantifiedBool (sAnd (map boolOf by) .=> quantifiedBool p)

        good = do putStrLn $ drop (length nm) $ tag tab nm "Q.E.D."
                  pure $ ProvenBool (quantifiedBool p)

        cex  = do putStrLn $ "\n*** Failed to prove " ++ nm ++ "."
                  -- Calculate as a sat call on negation, but print as a theorem
                  -- This allows for much better display of results.
                  SatResult res <- satWith cfg (skolemize (qNot p))
                  print $ ThmResult res
                  error "Failed"

        failed r = do putStrLn $ "\n*** Failed to prove " ++ nm ++ "."
                      print r
                      error "Failed"

    pRes <- proveWith cfg proposition
    case pRes of
      ThmResult Unsatisfiable{} -> good
      ThmResult Satisfiable{}   -> cex
      ThmResult DeltaSat{}      -> cex
      ThmResult SatExtField{}   -> cex
      ThmResult Unknown{}       -> failed pRes
      ThmResult ProofError{}    -> failed pRes

-- | Prove a given statement, using auxiliaries as helpers. Using the default solver.
lemma :: Proposition a => String -> a -> [Proven] -> IO Proven
lemma = lemmaGen defaultSMTCfg "Lemma: "

-- | Prove a given statement, using auxiliaries as helpers. Using the given solver.
lemmaWith :: Proposition a => SMTConfig -> String -> a -> [Proven] -> IO Proven
lemmaWith cfg = lemmaGen cfg "Lemma: "

-- | Prove a given statement, using auxiliaries as helpers. Essentially the same as 'lemma', except for the name, using the default solver.
theorem :: Proposition a => String -> a -> [Proven] -> IO Proven
theorem = lemmaGen defaultSMTCfg "Theorem: "

-- | Prove a given statement, using auxiliaries as helpers. Essentially the same as 'lemmaWith', except for the name.
theoremWith :: Proposition a => SMTConfig -> String -> a -> [Proven] -> IO Proven
theoremWith cfg = lemmaGen cfg "Theorem: "

-- | A class for doing equational reasoning style chained proofs. Use 'chainLemma' to prove a given theorem
-- as a sequence of equalities, each step following from the previous.
class ChainLemma steps step | steps -> step where

  -- | Prove a property via a series of equality steps, using the default solver.
  -- Let @H@ be a list of already established lemmas. Let @P@ be a property we wanted to prove, named @name@.
  -- Given a call of the form @chainLemma name P [A, B, C, D] H@, we proceed as follows:
  --
  --    * Prove: @H -> A == B@
  --    * Prove: @H && A == B -> B == C@
  --    * Prove: @H && A == B && B == C -> C == D@
  --    * Prove: @H && A == B && B == C && C == D -> P@
  --    * If all of the above steps succeed, conclude @P@.
  --
  -- So, chain-lemma is essentially modus-ponens, applied in a sequence of stepwise equality reasoning.
  --
  -- There must be at least 2 steps given, as no helpers is equivalent to 'lemma' and a single step
  -- wouldn't be helpful since there's no equality to establish first.
  chainLemma :: Proposition a => String -> a -> steps -> [Proven] -> IO Proven

  -- | Prove a property via a series of equality steps, using the given solver.
  chainLemmaWith :: Proposition a => SMTConfig -> String -> a -> steps -> [Proven] -> IO Proven

  -- | Internal, shouldn't be needed outside the library
  makeSteps  :: steps -> [step]
  makeInter  :: steps -> step -> step -> SBool

  chainLemma = chainLemmaWith defaultSMTCfg

  chainLemmaWith cfg nm result steps base = do
        void (start (verbose cfg) "Chain: " (nm ++ "\n"))
        let proofSteps = makeSteps steps
            len        = length proofSteps
        when (len < 2) $
         error $ unlines $ [ "Incorrect use of chainLemma on " ++ show nm ++ ":"
                           , "   ** There must be at least two steps."
                           , "   ** Saw " ++ show len ++ " step(s) only."
                           ]
        go (1 :: Int) base proofSteps
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
