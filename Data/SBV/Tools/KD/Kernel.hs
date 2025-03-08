-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.KD.Kernel
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

module Data.SBV.Tools.KD.Kernel (
         Proposition,  Proof(..)
       , axiom
       , lemma,   lemmaWith,   lemmaGen
       , theorem, theoremWith
       , sorry
       , internalAxiom
       , checkSatThen
       ) where

import Control.Monad.Trans  (liftIO, MonadIO)

import Data.List  (intercalate)
import Data.Maybe (catMaybes, fromMaybe)

import Data.SBV.Core.Data hiding (None)
import Data.SBV.Core.Symbolic (isEmptyModel)
import Data.SBV.Trans.Control hiding (getProof)

import Data.SBV.SMT.SMT
import Data.SBV.Core.Model
import Data.SBV.Provers.Prover

import Data.SBV.Tools.KD.Utils

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
                _   <- liftIO $ startKD cfg True "Axiom" [nm]
                pure (internalAxiom nm p) { isUserAxiom = True }

-- | Internal axiom generator; so we can keep truck of KnuckleDrugger's trusted axioms, vs. user given axioms.
internalAxiom :: Proposition a => String -> a -> Proof
internalAxiom nm p = Proof { rootOfTrust = None
                           , isUserAxiom = False
                           , getProof    = label nm (quantifiedBool p)
                           , getProp     = toDyn p
                           , proofName   = nm
                           }

-- | A manifestly false theorem. This is useful when we want to prove a theorem that the underlying solver
-- cannot deal with, or if we want to postpone the proof for the time being. KnuckleDragger will keep
-- track of the uses of 'sorry' and will print them appropriately while printing proofs.
sorry :: Proof
sorry = Proof { rootOfTrust = Self
              , isUserAxiom = False
              , getProof    = label "sorry" (quantifiedBool p)
              , getProp     = toDyn p
              , proofName   = "sorry"
              }
  where -- ideally, I'd rather just use
        --   p = sFalse
        -- but then SBV constant folds the boolean, and the generated script
        -- doesn't contain the actual contents, as SBV determines unsatisfiability
        -- itself. By using the following proposition (which is easy for the backend
        -- solver to determine as false, we avoid the constant folding.
        p (Forall @"__sbvKD_sorry" (x :: SBool)) = label "SORRY: KnuckleDragger, proof uses \"sorry\"" x

-- | Helper to generate lemma/theorem statements.
lemmaGen :: Proposition a => SMTConfig -> String -> [String] -> a -> [Proof] -> KD Proof
lemmaGen cfg@SMTConfig{kdOptions = KDOptions{measureTime}} tag nms inputProp by = do
        kdSt <- getKDState
        liftIO $ getTimeStampIf measureTime >>= runSMTWith cfg . go kdSt
  where go kdSt mbStartTime = do qSaturateSavingObservables inputProp
                                 mapM_ (constrain . getProof) by
                                 query $ checkSatThen cfg kdSt tag False Nothing inputProp by nms Nothing Nothing (good mbStartTime)

        -- What to do if all goes well
        good mbStart d = do mbElapsed <- getElapsedTime mbStart
                            liftIO $ finishKD cfg ("Q.E.D." ++ modulo) d $ catMaybes [mbElapsed]
                            pure Proof { rootOfTrust = ros
                                       , isUserAxiom = False
                                       , getProof    = label nm (quantifiedBool inputProp)
                                       , getProp     = toDyn inputProp
                                       , proofName   = nm
                                       }
          where (ros, modulo) = calculateRootOfTrust nm by
                nm = intercalate "." nms

-- | Prove a given statement, using auxiliaries as helpers. Using the default solver.
lemma :: Proposition a => String -> a -> [Proof] -> KD Proof
lemma nm f by = do cfg <- getKDConfig
                   lemmaWith cfg nm f by

-- | Prove a given statement, using auxiliaries as helpers. Using the given solver.
lemmaWith :: Proposition a => SMTConfig -> String -> a -> [Proof] -> KD Proof
lemmaWith cfg nm = lemmaGen cfg "Lemma" [nm]

-- | Prove a given statement, using auxiliaries as helpers. Essentially the same as 'lemma', except for the name, using the default solver.
theorem :: Proposition a => String -> a -> [Proof] -> KD Proof
theorem nm f by = do cfg <- getKDConfig
                     theoremWith cfg nm f by

-- | Prove a given statement, using auxiliaries as helpers. Essentially the same as 'lemmaWith', except for the name.
theoremWith :: Proposition a => SMTConfig -> String -> a -> [Proof] -> KD Proof
theoremWith cfg nm = lemmaGen cfg "Theorem" [nm]

-- | Capture the general flow after a checkSat. We run the sat case if model is empty.
-- NB. This is the only place in Knuckledragger where we actually call check-sat;
-- so all interaction goes through here.
checkSatThen :: (SolverContext m, MonadIO m, MonadQuery m, Proposition a)
   => SMTConfig                              -- ^ config
   -> KDState                                -- ^ KDState
   -> String                                 -- ^ tag
   -> Bool                                   -- in query mode already (True), or lemmaGen (False)?
   -> Maybe SBool                            -- ^ context if any. If there's one we'll push/pop
   -> a                                      -- ^ what we want to prove
   -> [Proof]                                -- ^ helpers in the context. NB. Only used for printing cex's. We assume they're already asserted.
   -> [String]                               -- ^ sub-proof
   -> Maybe [String]                         -- ^ full-path to the proof, if different than sub-proof
   -> Maybe (IO ())                          -- ^ special code to run if model is empty (if any)
   -> ((Int, Maybe NominalDiffTime) -> IO r) -- ^ what to do when unsat, with the tab amount and time elapsed (if asked)
   -> m r
checkSatThen cfg@SMTConfig{verbose, kdOptions = KDOptions{measureTime}} kdState tag inQuery mbCtx prop by nms fullNms mbSat unsat = do

        case mbCtx of
           Just{}  -> inNewAssertionStack check
           Nothing -> check

 where check = do
           tab <- liftIO $ startKD cfg verbose tag nms

           case mbCtx of
             Nothing  -> queryDebug ["; checkSatThen: No context value to push."]
             Just ctx -> do queryDebug ["; checkSatThen: Pushing in the context: " ++ show ctx]
                            constrain ctx

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

       fullNm = intercalate "." $ squeeze $ filter (not . null) (fromMaybe nms fullNms)
       squeeze (x:y:rest) | x == y = squeeze (y:rest)
       squeeze (x:rest)            = x : squeeze rest
       squeeze []                  = []

       unknown = do r <- getUnknownReason
                    liftIO $ do putStrLn $ "\n*** Failed to prove " ++ fullNm ++ "."
                                putStrLn $ "\n*** Solver reported: " ++ show r
                                die

       -- What to do if the proof fails
       cex  = do liftIO $ putStrLn $ "\n*** Failed to prove " ++ fullNm ++ "."

                 res <- if inQuery
                        then Satisfiable cfg <$> getModel
                        else -- When trying to get a counter-example not in query mode, we
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

                 let isEmpty = case res of
                                 Unsatisfiable{} -> -- Shouldn't really happen! bail out
                                                    error $ unlines [" SBV.KnuckleDragger: Unexpected unsat-result while extracting a model."
                                                                    , "Please report this as a bug!"
                                                                    ]
                                 Satisfiable _ m -> isEmptyModel m  -- Expected case
                                 DeltaSat _ _  m -> isEmptyModel m  -- Unlikely but why not
                                 SatExtField _ m -> isEmptyModel m  -- Can't really happen
                                 Unknown{}       -> False           -- Possible, I suppose. Just print it
                                 ProofError{}    -> False           -- Ditto

                 liftIO $ case (isEmpty, mbSat) of
                           (True,  Just act) -> act
                           _                 -> print $ ThmResult res

                 die
