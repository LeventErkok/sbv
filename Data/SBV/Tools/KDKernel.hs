-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.KDKernel
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Kernel of the KnuckleDragger prover API.
-----------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE ScopedTypeVariables  #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.KDKernel (
         Proposition,  Proof(..)
       , axiom
       , lemma,   lemmaWith,   lemmaGen
       , theorem, theoremWith
       , sorry
       ) where

import Control.Monad.Trans  (liftIO)
import Control.Monad.Reader (ask)

import Data.List (intercalate)

import Data.SBV
import Data.SBV.Core.Data (Constraint)

import Data.SBV.Tools.KDUtils

-- | A proposition is something SBV is capable of proving/disproving. We capture this
-- with a set of constraints. This type might look scary, but for the most part you
-- can ignore it and treat it as anything you can pass to 'prove' or 'sat' in SBV.
type Proposition a = ( QuantifiedBool a
                     , QNot a
                     , Skolemize (NegatesTo a)
                     , Satisfiable (Symbolic (SkolemsTo (NegatesTo a)))
                     , Constraint  Symbolic  (SkolemsTo (NegatesTo a))
                     )

-- | Accept the given definition as a fact. Usually used to introduce definitial axioms,
-- giving meaning to uninterpreted symbols. Note that we perform no checks on these propositions,
-- if you assert nonsense, then you get nonsense back. So, calls to 'axiom' should be limited to
-- definitions, or basic axioms (like commutativity, associativity) of uninterpreted function symbols.
axiom :: Proposition a => String -> a -> KD Proof
axiom nm p = do start False "Axiom" [nm] >>= finish "Axiom."

                pure (internalAxiom nm p) { isUserAxiom = True }

-- | Internal axiom generator; so we can keep truck of KnuckleDrugger's trusted axioms, vs. user given axioms.
-- Not exported.
internalAxiom :: Proposition a => String -> a -> Proof
internalAxiom nm p = Proof { rootOfTrust = None
                           , isUserAxiom = False
                           , getProof    = label nm (quantifiedBool p)
                           , proofName   = nm
                           }

-- | A manifestly false theorem. This is useful when we want to prove a theorem that the underlying solver
-- cannot deal with, or if we want to postpone the proof for the time being. KnuckleDragger will keep
-- track of the uses of 'sorry' and will print them appropriately while printing proofs.
sorry :: Proof
sorry = Proof { rootOfTrust = Self
              , isUserAxiom = False
              , getProof    = label "sorry" (quantifiedBool p)
              , proofName   = "sorry"
              }
  where -- ideally, I'd rather just use 
        --   p = sFalse
        -- but then SBV constant folds the boolean, and the generated script
        -- doesn't contain the actual contents, as SBV determines unsatisfiability
        -- itself. By using the following proposition (which is easy for the backend
        -- solver to determine as false, we avoid the constant folding.
        p (Forall (x :: SBool)) = label "SORRY: KnuckleDragger, proof uses \"sorry\"" x

-- | Helper to generate lemma/theorem statements.
lemmaGen :: Proposition a => SMTConfig -> String -> [String] -> a -> [Proof] -> KD Proof
lemmaGen cfg@SMTConfig{verbose} what nms inputProp by = do
    tab <- start verbose what nms

    let nm = intercalate "." nms

        -- What to do if all goes well
        good = do finish ("Q.E.D." ++ modulo) tab
                  pure Proof { rootOfTrust = ros
                             , isUserAxiom = False
                             , getProof    = label nm (quantifiedBool inputProp)
                             , proofName   = nm
                             }
          where (ros, modulo) = calculateRootOfTrust nm by

        -- What to do if the proof fails
        cex  = liftIO $ do putStrLn $ "\n*** Failed to prove " ++ nm ++ "."

                           -- When trying to get a counter-example, only include in the
                           -- implication those facts that are user-given axioms. This
                           -- way our counter-example will be more likely to be relevant
                           -- to the proposition we're currently proving. (Hopefully.)
                           -- Remember that we first have to negate, and then skolemize!
                           SatResult res <- satWith cfg $ do
                                               mapM_ constrain [getProof | Proof{isUserAxiom, getProof} <- by, isUserAxiom] :: Symbolic ()
                                               pure $ skolemize (qNot inputProp)

                           print $ ThmResult res
                           error "Failed"

        -- bailing out
        failed r = liftIO $ do putStrLn $ "\n*** Failed to prove " ++ nm ++ "."
                               print r
                               error "Failed"

    pRes <- liftIO $ proveWith cfg $ do
                mapM_ (constrain . getProof) by :: Symbolic ()
                pure $ skolemize (quantifiedBool inputProp)

    case pRes of
      ThmResult Unsatisfiable{} -> good
      ThmResult Satisfiable{}   -> cex
      ThmResult DeltaSat{}      -> cex
      ThmResult SatExtField{}   -> cex
      ThmResult Unknown{}       -> failed pRes
      ThmResult ProofError{}    -> failed pRes

-- | Prove a given statement, using auxiliaries as helpers. Using the default solver.
lemma :: Proposition a => String -> a -> [Proof] -> KD Proof
lemma nm f by = do cfg <- ask
                   lemmaWith cfg nm f by

-- | Prove a given statement, using auxiliaries as helpers. Using the given solver.
lemmaWith :: Proposition a => SMTConfig -> String -> a -> [Proof] -> KD Proof
lemmaWith cfg nm = lemmaGen cfg "Lemma" [nm]

-- | Prove a given statement, using auxiliaries as helpers. Essentially the same as 'lemma', except for the name, using the default solver.
theorem :: Proposition a => String -> a -> [Proof] -> KD Proof
theorem nm f by = do cfg <- ask
                     theoremWith cfg nm f by

-- | Prove a given statement, using auxiliaries as helpers. Essentially the same as 'lemmaWith', except for the name.
theoremWith :: Proposition a => SMTConfig -> String -> a -> [Proof] -> KD Proof
theoremWith cfg nm = lemmaGen cfg "Theorem" [nm]
