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
-- Example uses:
--
--    * Proving Kleene algebra properties: "Documentation.SBV.Examples.KnuckleDragger.Kleene"
--    * Several induction examples over naturals and lists: "Documentation.SBV.Examples.KnuckleDragger.Induction"
--    * Proving square-root-of-2 is irrational: "Documentation.SBV.Examples.KnuckleDragger.Sqrt2IsIrrational"
-----------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.KnuckleDragger (
       -- * Propositions and proven statements
         Proposition,  Proven
       -- * Adding axioms/definitions
       , axiom
       -- * Basic proofs
       , lemma,        lemmaWith
       , theorem,      theoremWith
       -- * Chain of reasoning
       , chainLemma,   chainLemmaWith
       , chainTheorem, chainTheoremWith
       -- * Induction
       , Induction(..)
       -- * Faking proofs
       , sorry
       ) where

import Data.List (intercalate)

import Data.SBV
import Data.SBV.Core.Data (Constraint)

import qualified Data.SBV.List as SL

import Control.Monad(when, void)

-- | A proposition is something SBV is capable of proving/disproving. We capture this
-- with a set of constraints. This type might look scary, but for the most part you
-- can ignore it and treat it as anything you can pass to 'prove' or 'sat' in SBV.
type Proposition a = ( QuantifiedBool a
                     , QNot a
                     , Satisfiable (SkolemsTo (NegatesTo a))
                     , Constraint Symbolic (SkolemsTo (NegatesTo a))
                     , Skolemize (NegatesTo a)
                     )

-- | Start a proof. We return the number of characters we printed, so the finisher can align the result.
start :: Bool -> String -> [String] -> IO Int
start newLine what nms = do putStr $ line ++ if newLine then "\n" else ""
                            return (length line)
  where tab    = 2 * length (drop 1 nms)
        indent = replicate tab ' '
        tag    = what ++ ": " ++ intercalate "." nms
        line   = indent ++ tag

-- | Finish a proof. First argument is what we got from the call of 'start' above.
finish :: String -> Int -> IO ()
finish what skip = putStrLn $ replicate (ribbonLength - skip) ' ' ++ what
  where -- Ideally an aestheticly pleasing length of the line. Perhaps this
        -- should be configurable, but this is good enough for now.
        ribbonLength :: Int
        ribbonLength = 50

-- | A proven property. This type is left abstract, i.e., the only way to create on is via a
-- call to 'lemma'/'theorem' etc., ensuring soundness. (Note that the trusted-code base here
-- is still large: The underlying solver, SBV, and KnuckleDragger kernel itself. But this
-- mechanism ensures we can't create proven things out of thin air, following the standard LCF
-- methodology.)
data Proven = ProvenBool { boolOf :: SBool }

-- | Accept the given definition as a fact. Usually used to introduce definitial axioms,
-- giving meaning to uninterpreted symbols. Note that we perform no checks on these propositions,
-- if you assert nonsense, then you get nonsense back. So, calls to 'axiom' should be limited to
-- definitions, or basic axioms (like commutativity, associativity) of uninterpreted function symbols.
axiom :: Proposition a => String -> a -> IO Proven
axiom nm p = do start False "Axiom" [nm] >>= finish "Admitted."
                pure $ ProvenBool (quantifiedBool p)

-- | Blindly believe a proposition as a theorem. This is in essence the same as 'axiom', except
-- it serves for documentation purposes that it should be provable. It's useful during development,
-- and also when you hit a theorem that the underlying solver just can't handle.
-- giving meaning to uninterpreted symbols. The list argument is unused, but it makes the
-- signature similar to 'lemma', allowing replacing `lemma` and `sorry` easily during development process.
sorry :: Proposition a => String -> a -> [b] -> IO Proven
sorry nm p _bu = do start False "Sorry" [nm] >>= finish "Blindly believed."
                    pure $ ProvenBool (quantifiedBool p)

-- | Helper to generate lemma/theorem statements.
lemmaGen :: Proposition a => SMTConfig -> String -> [String] -> a -> [Proven] -> IO Proven
lemmaGen cfg what nms p by = do
    tab <- start (verbose cfg) what nms

    let proposition = quantifiedBool (sAnd (map boolOf by) .=> quantifiedBool p)

        good = do finish "Q.E.D." tab
                  pure $ ProvenBool (quantifiedBool p)

        cex  = do putStrLn $ "\n*** Failed to prove " ++ intercalate "." nms ++ "."
                  -- Calculate as a sat call on negation, but print as a theorem
                  -- This allows for much better display of results.
                  SatResult res <- satWith cfg (skolemize (qNot p))
                  print $ ThmResult res
                  error "Failed"

        failed r = do putStrLn $ "\n*** Failed to prove " ++ intercalate "." nms ++ "."
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
lemma nm = lemmaGen defaultSMTCfg "Lemma" [nm]

-- | Prove a given statement, using auxiliaries as helpers. Using the given solver.
lemmaWith :: Proposition a => SMTConfig -> String -> a -> [Proven] -> IO Proven
lemmaWith cfg nm = lemmaGen cfg "Lemma" [nm]

-- | Prove a given statement, using auxiliaries as helpers. Essentially the same as 'lemma', except for the name, using the default solver.
theorem :: Proposition a => String -> a -> [Proven] -> IO Proven
theorem nm = lemmaGen defaultSMTCfg "Theorem" [nm]

-- | Prove a given statement, using auxiliaries as helpers. Essentially the same as 'lemmaWith', except for the name.
theoremWith :: Proposition a => SMTConfig -> String -> a -> [Proven] -> IO Proven
theoremWith cfg nm = lemmaGen cfg "Theorem" [nm]

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
  -- So, chain-lemma is essentially modus-ponens, applied in a sequence of stepwise equality reasoning.
  --
  -- If there are no helpers given (i.e., if @H@ is empty), then this call is equivalent to 'lemmaWith'.
  -- If @H@ is a singleton, then we error-out. A single step in @H@ indicates a user-error, since there's
  -- no sequence of steps to reason about.
  chainLemma :: Proposition a => String -> a -> steps -> [Proven] -> IO Proven

  -- | Same as chainLemma, except tagged as Theorem
  chainTheorem :: Proposition a => String -> a -> steps -> [Proven] -> IO Proven

  -- | Prove a property via a series of equality steps, using the given solver.
  chainLemmaWith :: Proposition a => SMTConfig -> String -> a -> steps -> [Proven] -> IO Proven

  -- | Same as chainLemmaWith, except tagged as Theorem
  chainTheoremWith :: Proposition a => SMTConfig -> String -> a -> steps -> [Proven] -> IO Proven

  -- | Internal, shouldn't be needed outside the library
  makeSteps  :: steps -> [step]
  makeInter  :: steps -> step -> step -> SBool

  chainLemma   = chainLemmaWith   defaultSMTCfg
  chainTheorem = chainTheoremWith defaultSMTCfg

  chainLemmaWith   = chainGeneric False
  chainTheoremWith = chainGeneric True

  chainGeneric :: Proposition a => Bool -> SMTConfig -> String -> a -> steps -> [Proven] -> IO Proven
  chainGeneric taggedTheorem cfg nm result steps base = do
        void (start True "Chain" [nm])
        let proofSteps = makeSteps steps
            len        = length proofSteps
        when (len == 1) $
         error $ unlines $ [ "Incorrect use of chainLemma on " ++ show nm ++ ":"
                           , "   ** There must be either none, or at least two steps."
                           , "   ** Was given only one step."
                           ]
        go (1 :: Int) base (zipWith (makeInter steps) proofSteps (drop 1 proofSteps))
     where go _ sofar []
              | taggedTheorem = theoremWith cfg nm result sofar
              | True          = lemmaWith   cfg nm result sofar
           go i sofar (p:ps)
            | True
            = do step <- lemmaGen cfg "Lemma" ([nm, show i]) p sofar
                 go (i+1) (step : sofar) ps

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

-- | Given a predicate, return an induction principle for it. Typically, we only have one viable
-- induction principle for a given type, but we allow for alternative ones.
class Induction a where
  inductionPrinciple  :: (a -> SBool) -> IO Proven
  inductionPrinciple2 :: (a -> SBool) -> IO Proven
  inductionPrinciple3 :: (a -> SBool) -> IO Proven

  -- The second and third principles are the same as first by default, unless we provide them
  -- explicitly.
  inductionPrinciple2 = inductionPrinciple
  inductionPrinciple3 = inductionPrinciple

-- | Induction over SInteger. We provide various induction principles here: The first one
-- is over naturals, will only prove predicates that explicitly restrict the argument to >= 0.
-- The second and third ones are induction over the entire range of integers, two different
-- principles that might work better for different problems.
instance Induction SInteger where

   -- | Induction over naturals. Will prove predicates of the form @\n -> n >= 0 .=> predicate n@.
   inductionPrinciple p = do
      let qb = quantifiedBool

          principle =       p 0 .&& qb (\(Forall n) -> (n .>= 0 .&& p n) .=> p (n+1))
                    .=> qb -----------------------------------------------------------
                                      (\(Forall n) -> n .>= 0 .=> p n)

      axiom "Nat.induction" principle

   -- | Induction over integers, using the strategy that @P(n)@ is equivalent to @P(n+1)@
   -- (i.e., not just @P(n) => P(n+1)@), thus covering the entire range.
   inductionPrinciple2 p = do
      let qb = quantifiedBool

          principle =       p 0 .&& qb (\(Forall i) -> p i .== p (i+1))
                    .=> qb ---------------------------------------------
                                    (\(Forall i) -> p i)

      axiom "Integer.induction" principle

   -- | Induction over integers, using the strategy that @P(n) => P(n+1)@ and @P(n) => P(n-1)@.
   inductionPrinciple3 p = do
      let qb = quantifiedBool

          principle =       p 0 .&& qb (\(Forall i) -> p i .=> p (i+1) .&& p (i-1))
                    .=> qb ---------------------------------------------------------
                                           (\(Forall i) -> p i)

      axiom "Integer.splitInduction" principle

-- | Induction over lists
instance SymVal a => Induction (SList a) where
  inductionPrinciple p = do
     let qb a = quantifiedBool a

         principle =       p SL.nil .&& qb (\(Forall x) (Forall xs) -> p xs .=> p (x SL..: xs))
                   .=> qb ----------------------------------------------------------------------
                                             (\(Forall xs) -> p xs)

     axiom "List(a).induction" principle
