-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.TP.Kernel
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Kernel of the TP prover API.
-----------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeAbstractions     #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.TP.Kernel (
         Proposition,  Proof(..)
       , axiom
       , lemma
       , lemmaWith
       , internalAxiom
       , TPProofContext (..), smtProofStep
       ) where

import Control.Monad.Trans  (liftIO, MonadIO)

import Data.List  (intercalate)
import Data.Maybe (catMaybes)

import Data.SBV.Core.Data     hiding (None)
import Data.SBV.Trans.Control hiding (getProof)
import Data.SBV.Core.Symbolic (MonadSymbolic)

import Data.SBV.SMT.SMT
import Data.SBV.Core.Model
import Data.SBV.Provers.Prover

import Data.SBV.TP.Utils

import Data.Time (NominalDiffTime)
import Data.SBV.Utils.TDiff

import Data.Dynamic

-- | A proposition is something SBV is capable of proving/disproving in TP.
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
axiom :: Proposition a => String -> a -> TP (Proof a)
axiom nm p = do cfg <- getTPConfig
                u   <- tpGetNextUnique
                _   <- liftIO $ startTP cfg True "Axiom" 0 (TPProofOneShot nm [])
                let Proof iax = internalAxiom nm p
                pure $ Proof (iax { isUserAxiom = True, uniqId = u })

-- | Internal axiom generator; so we can keep truck of TP's trusted axioms, vs. user given axioms.
internalAxiom :: Proposition a => String -> a -> Proof a
internalAxiom nm p = Proof $ ProofObj { dependencies = []
                                      , isUserAxiom  = False
                                      , getObjProof  = label nm (quantifiedBool p)
                                      , getProp      = toDyn p
                                      , proofName    = nm
                                      , uniqId       = TPInternal
                                      , isCached     = False
                                      }

-- | Prove a lemma, using the given configuration
lemmaWith :: Proposition a => SMTConfig -> String -> a -> [ProofObj] -> TP (Proof a)
lemmaWith cfg@SMTConfig{tpOptions = TPOptions{printStats}} nm inputProp by = withProofCache nm $ do
                 tpSt <- getTPState
                 u    <- tpGetNextUnique
                 liftIO $ getTimeStampIf printStats >>= runSMTWith cfg . go tpSt u
  where go tpSt u mbStartTime = do qSaturateSavingObservables inputProp
                                   mapM_ (constrain . getObjProof) by
                                   query $ smtProofStep cfg tpSt "Lemma" 0 (TPProofOneShot nm by) Nothing inputProp [] (good mbStartTime u)

        -- What to do if all goes well
        good mbStart u d = do mbElapsed <- getElapsedTime mbStart
                              liftIO $ finishTP cfg ("Q.E.D." ++ concludeModulo by) d $ catMaybes [mbElapsed]
                              pure $ Proof $ ProofObj { dependencies = by
                                                      , isUserAxiom  = False
                                                      , getObjProof  = label nm (quantifiedBool inputProp)
                                                      , getProp      = toDyn inputProp
                                                      , proofName    = nm
                                                      , uniqId       = u
                                                      , isCached     = False
                                                      }

-- | Prove a given statement, using auxiliaries as helpers. Using the default solver.
lemma :: Proposition a => String -> a -> [ProofObj] -> TP (Proof a)
lemma nm f by = do cfg <- getTPConfig
                   lemmaWith cfg nm f by

-- | Capture the general flow of a proof-step. Note that this is the only point where we call the backend solver
-- in a TP proof.
smtProofStep :: (SolverContext m, MonadIO m, MonadQuery m, MonadSymbolic m, Proposition a)
   => SMTConfig                              -- ^ config
   -> TPState                                -- ^ TPState
   -> String                                 -- ^ tag
   -> Int                                    -- ^ level
   -> TPProofContext                         -- ^ the context in which we're doing the proof
   -> Maybe SBool                            -- ^ Assumptions under which we do the check-sat. If there's one we'll push/pop
   -> a                                      -- ^ what we want to prove
   -> [(String, SVal)]                       -- ^ Values to display in case of failure
   -> ((Int, Maybe NominalDiffTime) -> IO r) -- ^ what to do when unsat, with the tab amount and time elapsed (if asked)
   -> m r
smtProofStep cfg@SMTConfig{verbose, tpOptions = TPOptions{printStats}} tpState tag level ctx mbAssumptions prop disps unsat = do

        case mbAssumptions of
           Nothing  -> do queryDebug ["; smtProofStep: No context value to push."]
                          check
           Just asm -> do queryDebug ["; smtProofStep: Pushing in the context: " ++ show asm]
                          inNewAssertionStack $ do constrain asm
                                                   check

 where check = do
           tab <- liftIO $ startTP cfg verbose tag level ctx

           -- It's tempting to skolemize here.. But skolemization creates fresh constants
           -- based on the name given, and they mess with all else. So, don't skolemize!
           constrain $ sNot (quantifiedBool prop)

           (mbT, r) <- timeIf printStats checkSat

           updStats tpState (\s -> s{noOfCheckSats = noOfCheckSats s + 1})

           case mbT of
             Nothing -> pure ()
             Just t  -> updStats tpState (\s -> s{solverElapsed = solverElapsed s + t})

           case r of
             Unk    -> unknown
             Sat    -> cex
             DSat{} -> cex
             Unsat  -> liftIO $ unsat (tab, mbT)

       die = error "Failed"

       fullNm = case ctx of
                  TPProofOneShot       s _    -> s
                  TPProofStep    True  s _ ss -> "assumptions for " ++ intercalate "." (s : ss)
                  TPProofStep    False s _ ss ->                       intercalate "." (s : ss)

       unknown = do r <- getUnknownReason
                    liftIO $ do putStrLn $ "\n*** Failed to prove " ++ fullNm ++ "."
                                putStrLn $ "\n*** Solver reported: " ++ show r
                                die

       -- What to do if the proof fails
       cex = do
         liftIO $ putStrLn $ "\n*** Failed to prove " ++ fullNm ++ "."

         res <- case ctx of
                  TPProofStep{} -> do mapM_ (uncurry sObserve) disps
                                      Satisfiable cfg <$> getModel
                  TPProofOneShot _ by ->
                     -- When trying to get a counter-example not in query mode, we
                     -- do a skolemized sat call, which gets better counter-examples.
                     -- We only include the those facts that are user-given axioms. This
                     -- way our counter-example will be more likely to be relevant
                     -- to the proposition we're currently proving. (Hopefully.)
                     -- Remember that we first have to negate, and then skolemize!
                     do SatResult res <- liftIO $ satWith cfg $ do
                                           qSaturateSavingObservables prop
                                           mapM_ constrain [getObjProof | ProofObj{isUserAxiom, getObjProof} <- by, isUserAxiom] :: Symbolic ()
                                           mapM_ (uncurry sObserve) disps
                                           pure $ skolemize (qNot prop)
                        pure res

         liftIO $ print $ ThmResult res

         die
