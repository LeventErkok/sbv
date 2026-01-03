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

{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.TP.Kernel (
         Proposition,  Proof(..)
       , axiom
       , lemma,          lemmaWith
       , inductiveLemma, inductiveLemmaWith
       , internalAxiom
       , TPProofContext (..), smtProofStep, HasInductionSchema(..)
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

import Type.Reflection (typeRep)

import qualified Data.SBV.List as SL (nil, (.:))

-- | A proposition is something SBV is capable of proving/disproving in TP.
type Proposition a = ( QNot a
                     , QuantifiedBool a
                     , QSaturate Symbolic a
                     , Skolemize (NegatesTo a)
                     , Satisfiable (Symbolic (SkolemsTo (NegatesTo a)))
                     , Constraint  Symbolic  (SkolemsTo (NegatesTo a))
                     , Typeable a
                     )

-- | An inductive proposition is a proposition that has an induction scheme associated with it.
type Inductive a = (HasInductionSchema a, Proposition a)

-- | A class of values that has an associated induction schema. SBV manages this internally.
class HasInductionSchema a where
  inductionSchema :: a -> ProofObj

-- | Induction schema for integers. Note that this is good for proving properties over naturals really.
-- There are other instances that would apply to all integers, but this one is really the most useful
-- in practice.
instance HasInductionSchema (Forall nm Integer -> SBool) where
   inductionSchema p = proofOf $ internalAxiom "inductInteger" ax
     where pf = p . Forall
           ax =   sAnd [pf 0, quantifiedBool (\(Forall i) -> (i .>= 0 .=> pf i) .=> pf (i + 1))]
              .=> quantifiedBool (\(Forall i) -> pf i)

-- | Induction schema for integers with one extra argument
instance SymVal at => HasInductionSchema (Forall nm Integer -> Forall an at -> SBool) where
   inductionSchema p = proofOf $ internalAxiom "inductInteger1" ax
     where pf i a = p (Forall i) (Forall a)
           ax     = sAnd [ quantifiedBool (\           (Forall a) -> pf 0 a)
                         , quantifiedBool (\(Forall i) (Forall a) -> (i .>= 0 .=> pf i a) .=> pf (i + 1) a)]
                    .=>    quantifiedBool (\(Forall i) (Forall a) -> pf i a)

-- | Induction schema for integers with two extra arguments
instance (SymVal at, SymVal bt) => HasInductionSchema (Forall nm Integer -> Forall an at -> Forall bn bt -> SBool) where
   inductionSchema p = proofOf $ internalAxiom "inductInteger2" ax
     where pf i a b = p (Forall i) (Forall a) (Forall b)
           ax       = sAnd [ quantifiedBool (\           (Forall a) (Forall b) -> pf 0 a b)
                           , quantifiedBool (\(Forall i) (Forall a) (Forall b) -> (i .>= 0 .=> pf i a b) .=> pf (i + 1) a b)]
                      .=>    quantifiedBool (\(Forall i) (Forall a) (Forall b) -> pf i a b)

-- | Induction schema for integers with three extra arguments
instance (SymVal at, SymVal bt, SymVal ct) => HasInductionSchema (Forall nm Integer -> Forall an at -> Forall bn bt -> Forall cn ct -> SBool) where
   inductionSchema p = proofOf $ internalAxiom "inductInteger3" ax
     where pf i a b c = p (Forall i) (Forall a) (Forall b) (Forall c)
           ax         = sAnd [ quantifiedBool (\           (Forall a) (Forall b) (Forall c) -> pf 0 a b c)
                             , quantifiedBool (\(Forall i) (Forall a) (Forall b) (Forall c) -> (i .>= 0 .=> pf i a b c) .=> pf (i + 1) a b c)]
                        .=>    quantifiedBool (\(Forall i) (Forall a) (Forall b) (Forall c) -> pf i a b c)

-- | Induction schema for integers with four extra arguments
instance (SymVal at, SymVal bt, SymVal ct, SymVal dt) => HasInductionSchema (Forall nm Integer -> Forall an at -> Forall bn bt -> Forall cn ct -> Forall dn dt -> SBool) where
   inductionSchema p = proofOf $ internalAxiom "inductInteger4" ax
     where pf i a b c d = p (Forall i) (Forall a) (Forall b) (Forall c) (Forall d)
           ax           = sAnd [ quantifiedBool (\           (Forall a) (Forall b) (Forall c) (Forall d) -> pf 0 a b c d)
                               , quantifiedBool (\(Forall i) (Forall a) (Forall b) (Forall c) (Forall d) -> (i .>= 0 .=> pf i a b c d) .=> pf (i + 1) a b c d)]
                          .=>    quantifiedBool (\(Forall i) (Forall a) (Forall b) (Forall c) (Forall d) -> pf i a b c d)

-- | Induction schema for integers with five extra arguments
instance (SymVal at, SymVal bt, SymVal ct, SymVal dt, SymVal et) => HasInductionSchema (Forall nm Integer -> Forall an at -> Forall bn bt -> Forall cn ct -> Forall dn dt -> Forall en et -> SBool) where
   inductionSchema p = proofOf $ internalAxiom "inductInteger5" ax
     where pf i a b c d e = p (Forall i) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)
           ax             = sAnd [ quantifiedBool (\           (Forall a) (Forall b) (Forall c) (Forall d) (Forall e) -> pf 0 a b c d e)
                                 , quantifiedBool (\(Forall i) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e) -> (i .>= 0 .=> pf i a b c d e) .=> pf (i + 1) a b c d e)]
                            .=>    quantifiedBool (\(Forall i) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e) -> pf i a b c d e)

-- | Induction schema for lists.
instance SymVal x => HasInductionSchema (Forall nm [x] -> SBool) where
   inductionSchema p = proofOf $ internalAxiom ("induct" ++ show (typeRep @[x])) ax
     where pf = p . Forall
           ax =   sAnd [pf SL.nil, quantifiedBool (\(Forall x) (Forall xs) -> pf xs .=> pf (x SL..: xs))]
              .=> quantifiedBool (\(Forall xs) -> pf xs)

-- | Induction schema for lists with one extra argument
instance (SymVal x, SymVal at) => HasInductionSchema (Forall nm [x] -> Forall an at -> SBool) where
   inductionSchema p = proofOf $ internalAxiom ("induct" ++ show (typeRep @[x]) ++ "1") ax
     where pf xs a = p (Forall xs) (Forall a)
           ax      = sAnd [ quantifiedBool (\                       (Forall a) -> pf SL.nil a)
                          , quantifiedBool (\(Forall x) (Forall xs) (Forall a) -> pf xs a .=> pf (x SL..: xs) a)]
                     .=>    quantifiedBool (\(Forall xs) (Forall a) -> pf xs a)

-- | Induction schema for lists with two extra arguments
instance (SymVal x, SymVal at, SymVal bt) => HasInductionSchema (Forall nm [x] -> Forall an at -> Forall bn bt -> SBool) where
   inductionSchema p = proofOf $ internalAxiom ("induct" ++ show (typeRep @[x]) ++ "2") ax
     where pf xs a b = p (Forall xs) (Forall a) (Forall b)
           ax        = sAnd [ quantifiedBool (\                       (Forall a) (Forall b) -> pf SL.nil a b)
                            , quantifiedBool (\(Forall x) (Forall xs) (Forall a) (Forall b) -> pf xs a b .=> pf (x SL..: xs) a b)]
                       .=>    quantifiedBool (\(Forall xs) (Forall a) (Forall b) -> pf xs a b)

-- | Induction schema for lists with three extra arguments
instance (SymVal x, SymVal at, SymVal bt, SymVal ct) => HasInductionSchema (Forall nm [x] -> Forall an at -> Forall bn bt -> Forall cn ct -> SBool) where
   inductionSchema p = proofOf $ internalAxiom ("induct" ++ show (typeRep @[x]) ++ "3") ax
     where pf xs a b c = p (Forall xs) (Forall a) (Forall b) (Forall c)
           ax          = sAnd [ quantifiedBool (\                       (Forall a) (Forall b) (Forall c) -> pf SL.nil a b c)
                              , quantifiedBool (\(Forall x) (Forall xs) (Forall a) (Forall b) (Forall c) -> pf xs a b c .=> pf (x SL..: xs) a b c)]
                         .=>    quantifiedBool (\(Forall xs) (Forall a) (Forall b) (Forall c) -> pf xs a b c)

-- | Induction schema for lists with four extra arguments
instance (SymVal x, SymVal at, SymVal bt, SymVal ct, SymVal dt) => HasInductionSchema (Forall nm [x] -> Forall an at -> Forall bn bt -> Forall cn ct -> Forall dn dt -> SBool) where
   inductionSchema p = proofOf $ internalAxiom ("induct" ++ show (typeRep @[x]) ++ "4") ax
     where pf xs a b c d = p (Forall xs) (Forall a) (Forall b) (Forall c) (Forall d)
           ax            = sAnd [ quantifiedBool (\                       (Forall a) (Forall b) (Forall c) (Forall d) -> pf SL.nil a b c d)
                                , quantifiedBool (\(Forall x) (Forall xs) (Forall a) (Forall b) (Forall c) (Forall d) -> pf xs a b c d .=> pf (x SL..: xs) a b c d)]
                           .=>    quantifiedBool (\(Forall xs) (Forall a) (Forall b) (Forall c) (Forall d) -> pf xs a b c d)

-- | Induction schema for lists with five extra arguments
instance (SymVal x, SymVal at, SymVal bt, SymVal ct, SymVal dt, SymVal et) => HasInductionSchema (Forall nm [x] -> Forall an at -> Forall bn bt -> Forall cn ct -> Forall dn dt -> Forall en et -> SBool) where
   inductionSchema p = proofOf $ internalAxiom ("induct" ++ show (typeRep @[x]) ++ "5") ax
     where pf xs a b c d e = p (Forall xs) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)
           ax              = sAnd [ quantifiedBool (\                       (Forall a) (Forall b) (Forall c) (Forall d) (Forall e) -> pf SL.nil a b c d e)
                                  , quantifiedBool (\(Forall x) (Forall xs) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e) -> pf xs a b c d e .=> pf (x SL..: xs) a b c d e)]
                             .=>    quantifiedBool (\(Forall xs) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e) -> pf xs a b c d e)

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

-- | Merge TP configs, picking the TP specific settings from top
mergeTPConfig :: SMTConfig -> SMTConfig -> SMTConfig
mergeTPConfig cur top = cur{tpOptions = tpOptions top}

-- | Prove a lemma, using the given configuration
lemmaWith :: Proposition a => SMTConfig -> String -> a -> [ProofObj] -> TP (Proof a)
lemmaWith cfgIn nm inputProp by = withProofCache nm $ do
                 topCfg <- getTPConfig
                 let cfg@SMTConfig{tpOptions = TPOptions{printStats}} = cfgIn `mergeTPConfig` topCfg
                 tpSt <- getTPState
                 u    <- tpGetNextUnique
                 liftIO $ getTimeStampIf printStats >>= runSMTWith cfg . go tpSt cfg u
  where go tpSt cfg u mbStartTime = do qSaturateSavingObservables inputProp
                                       mapM_ (constrain . getObjProof) by
                                       query $ smtProofStep cfg tpSt "Lemma" 0 (TPProofOneShot nm by) Nothing inputProp [] (good cfg mbStartTime u)

        -- What to do if all goes well
        good cfg mbStart u d = do mbElapsed <- getElapsedTime mbStart
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

-- | Prove a given statement, using the induction schema for the proposition. Using the default solver.
inductiveLemma :: Inductive a => String -> a -> [ProofObj] -> TP (Proof a)
inductiveLemma nm f by = do cfg <- getTPConfig
                            inductiveLemmaWith cfg nm f by

-- | Prove a given statement, using the induction schema for the proposition. Using the default solver.
inductiveLemmaWith :: Inductive a => SMTConfig -> String -> a -> [ProofObj] -> TP (Proof a)
inductiveLemmaWith cfg nm f by = lemmaWith cfg nm f (inductionSchema f : by)

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
