-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.KnuckleDragger.Kernel
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Kernel of the KnuckleDragger prover API.
-----------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeAbstractions     #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.KnuckleDragger.Kernel (
         Proposition,  Proof(..)
       , axiom
       , lemma,   lemmaWith,   lemmaGen
       , theorem, theoremWith
       , internalAxiom
       , KDProofContext (..), smtProofStep
       ) where

import Control.Monad.Trans  (liftIO, MonadIO)

import Data.List  (intercalate)
import Data.Maybe (catMaybes)

import Data.SBV.Core.Data hiding (None)
import Data.SBV.Trans.Control hiding (getProof)

import Data.SBV.SMT.SMT
import Data.SBV.Core.Model
import Data.SBV.Provers.Prover

import Data.SBV.Tools.KnuckleDragger.Utils

import Data.Time (NominalDiffTime)
import Data.SBV.Utils.TDiff

import Data.Dynamic

-- | A proposition is something SBV is capable of proving/disproving in KnuckleDragger.
type Proposition a = ( QNot a
                     , QuantifiedBool a
                     , QSaturate Symbolic a
                     , Skolemize (NegatesTo a)
                     , Satisfiable (Symbolic (SkolemsTo (NegatesTo a)))
                     , Constraint  Symbolic  (SkolemsTo (NegatesTo a))
                     , Typeable a
                     )

-- | Accept the given definition as a fact. Usually used to introduce definitial axioms,
-- giving meaning to uninterpreted symbols. Note that we perform no checks on these propositions,
-- if you assert nonsense, then you get nonsense back. So, calls to 'axiom' should be limited to
-- definitions, or basic axioms (like commutativity, associativity) of uninterpreted function symbols.
axiom :: Proposition a => String -> a -> KD Proof
axiom nm p = do cfg <- getKDConfig
                u   <- kdGetNextUnique
                _   <- liftIO $ startKD cfg True "Axiom" 0 (KDProofOneShot nm [])
                pure (internalAxiom nm p) { isUserAxiom = True, uniqId = u }

-- | Internal axiom generator; so we can keep truck of KnuckleDrugger's trusted axioms, vs. user given axioms.
internalAxiom :: Proposition a => String -> a -> Proof
internalAxiom nm p = Proof { dependencies = []
                           , isUserAxiom  = False
                           , getProof     = label nm (quantifiedBool p)
                           , getProp      = toDyn p
                           , proofName    = nm
                           , uniqId       = KDInternal
                           }

-- | Helper to generate lemma/theorem statements.
lemmaGen :: Proposition a => SMTConfig -> String -> String -> a -> [Proof] -> KD Proof
lemmaGen cfg@SMTConfig{kdOptions = KDOptions{measureTime}} tag nm inputProp by = do
        kdSt <- getKDState
        u    <- kdGetNextUnique
        liftIO $ getTimeStampIf measureTime >>= runSMTWith cfg . go kdSt u
  where go kdSt u mbStartTime = do qSaturateSavingObservables inputProp
                                   mapM_ (constrain . getProof) by
                                   query $ smtProofStep cfg kdSt tag 0 (KDProofOneShot nm by) Nothing inputProp (good mbStartTime u)

        -- What to do if all goes well
        good mbStart u d = do mbElapsed <- getElapsedTime mbStart
                              liftIO $ finishKD cfg ("Q.E.D." ++ concludeModulo by) d $ catMaybes [mbElapsed]
                              pure Proof { dependencies = by
                                         , isUserAxiom  = False
                                         , getProof     = label nm (quantifiedBool inputProp)
                                         , getProp      = toDyn inputProp
                                         , proofName    = nm
                                         , uniqId       = u
                                         }

-- | Prove a given statement, using auxiliaries as helpers. Using the default solver.
lemma :: Proposition a => String -> a -> [Proof] -> KD Proof
lemma nm f by = do cfg <- getKDConfig
                   lemmaWith cfg nm f by

-- | Prove a given statement, using auxiliaries as helpers. Using the given solver.
lemmaWith :: Proposition a => SMTConfig -> String -> a -> [Proof] -> KD Proof
lemmaWith cfg = lemmaGen cfg "Lemma"

-- | Prove a given statement, using auxiliaries as helpers. Essentially the same as 'lemma', except for the name, using the default solver.
theorem :: Proposition a => String -> a -> [Proof] -> KD Proof
theorem nm f by = do cfg <- getKDConfig
                     theoremWith cfg nm f by

-- | Prove a given statement, using auxiliaries as helpers. Essentially the same as 'lemmaWith', except for the name.
theoremWith :: Proposition a => SMTConfig -> String -> a -> [Proof] -> KD Proof
theoremWith cfg = lemmaGen cfg "Theorem"

-- | Capture the general flow of a proof-step. Note that this is the only point where we call the backend solver
-- in a KD proof.
smtProofStep :: (SolverContext m, MonadIO m, MonadQuery m, Proposition a)
   => SMTConfig                              -- ^ config
   -> KDState                                -- ^ KDState
   -> String                                 -- ^ tag
   -> Int                                    -- ^ level
   -> KDProofContext                         -- ^ the context in which we're doing the proof
   -> Maybe SBool                            -- ^ Assumptions under which we do the check-sat. If there's one we'll push/pop
   -> a                                      -- ^ what we want to prove
   -> ((Int, Maybe NominalDiffTime) -> IO r) -- ^ what to do when unsat, with the tab amount and time elapsed (if asked)
   -> m r
smtProofStep cfg@SMTConfig{verbose, kdOptions = KDOptions{measureTime}} kdState tag level ctx mbAssumptions prop unsat = do

        case mbAssumptions of
           Nothing  -> do queryDebug ["; smtProofStep: No context value to push."]
                          check
           Just asm -> do queryDebug ["; smtProofStep: Pushing in the context: " ++ show asm]
                          inNewAssertionStack $ do constrain asm
                                                   check

 where check = do
           tab <- liftIO $ startKD cfg verbose tag level ctx

           -- It's tempting to skolemize here.. But skolemization creates fresh constants
           -- based on the name given, and they mess with all else. So, don't skolemize!
           constrain $ sNot (quantifiedBool prop)

           (mbT, r) <- timeIf measureTime checkSat

           updStats kdState (\s -> s{noOfCheckSats = noOfCheckSats s + 1})

           case mbT of
             Nothing -> pure ()
             Just t  -> updStats kdState (\s -> s{solverElapsed = solverElapsed s + t})

           case r of
             Unk    -> unknown
             Sat    -> cex
             DSat{} -> cex
             Unsat  -> liftIO $ unsat (tab, mbT)

       die = error "Failed"

       fullNm = case ctx of
                  KDProofOneShot       s _    -> s
                  KDProofStep    True  s _ ss -> "assumptions for " ++ intercalate "." (s : ss)
                  KDProofStep    False s _ ss ->                       intercalate "." (s : ss)

       unknown = do r <- getUnknownReason
                    liftIO $ do putStrLn $ "\n*** Failed to prove " ++ fullNm ++ "."
                                putStrLn $ "\n*** Solver reported: " ++ show r
                                die

       -- What to do if the proof fails
       cex = do
         liftIO $ putStrLn $ "\n*** Failed to prove " ++ fullNm ++ "."

         res <- case ctx of
                  KDProofStep{}       -> Satisfiable cfg <$> getModel
                  KDProofOneShot _ by ->
                     -- When trying to get a counter-example not in query mode, we
                     -- do a skolemized sat call, which gets better counter-examples.
                     -- We only include the those facts that are user-given axioms. This
                     -- way our counter-example will be more likely to be relevant
                     -- to the proposition we're currently proving. (Hopefully.)
                     -- Remember that we first have to negate, and then skolemize!
                     do SatResult res <- liftIO $ satWith cfg $ do
                                           qSaturateSavingObservables prop
                                           mapM_ constrain [getProof | Proof{isUserAxiom, getProof} <- by, isUserAxiom] :: Symbolic ()
                                           pure $ skolemize (qNot prop)
                        pure res

         liftIO $ print $ ThmResult res

         die
