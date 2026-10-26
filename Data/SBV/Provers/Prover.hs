-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Provers.Prover
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Provable abstraction and the connection to SMT solvers
-----------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Provers.Prover (
         SMTSolver(..), SMTConfig(..), Predicate
       , ProvableM(..), Provable, SatisfiableM(..), Satisfiable
       , generateSMTBenchmarkSat, generateSMTBenchmarkProof, defs2smt, ConstraintSet
       , ThmResult(..), SatResult(..), AllSatResult(..), SafeResult(..), OptimizeResult(..), SMTResult(..)
       , SExecutable(..), isSafe
       , runSMT, runSMTWith
       , SatModel(..), Modelable(..), displayModels, extractModels
       , getModelDictionaries, getModelValues
       , abc, boolector, bitwuzla, cvc4, cvc5, dReal, mathSAT, yices, z3, openSMT, defaultSMTCfg, defaultDeltaSMTCfg
       , proveWithAny, proveWithAll, proveConcurrentWithAny, proveConcurrentWithAll
       , satWithAny,   satWithAll,   satConcurrentWithAny,   satConcurrentWithAll
       ) where


import Control.Monad          (unless)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.DeepSeq        (rnf, NFData(..))

import Control.Concurrent.Async (async, waitAny, asyncThreadId, Async, mapConcurrently)
import Control.Exception (finally, throwTo)
import System.Exit (ExitCode(ExitSuccess))

import System.IO.Unsafe (unsafeInterleaveIO)             -- only used safely!

import System.Directory  (getCurrentDirectory)
import Data.Time (getZonedTime, NominalDiffTime, UTCTime, getCurrentTime, diffUTCTime)
import Data.List (intercalate, isPrefixOf, stripPrefix, genericIndex, genericLength)

import Data.Maybe (mapMaybe, listToMaybe, fromMaybe)

import Text.Read (readMaybe)

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set (empty)

import qualified Data.Foldable   as S (toList, foldl')
import qualified Data.Text       as T

import Data.SBV.Core.AlgReals (isExactRational)
import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic
import Data.SBV.Core.Operations
import Data.SBV.SMT.SMT
import Data.SBV.SMT.Utils (debug, alignPlain)
import Data.SBV.Utils.ExtractIO
import Data.SBV.Utils.Lib    (showText, unBar)
import Data.SBV.Utils.TDiff

import Data.SBV.Lambda () -- instances only

import qualified Data.SBV.Trans.Control as Control
import qualified Data.SBV.Control.Query as Control
import qualified Data.SBV.Control.Utils as Control

import GHC.Stack

import qualified Data.SBV.Provers.ABC       as ABC
import qualified Data.SBV.Provers.Boolector as Boolector
import qualified Data.SBV.Provers.Bitwuzla  as Bitwuzla
import qualified Data.SBV.Provers.CVC4      as CVC4
import qualified Data.SBV.Provers.CVC5      as CVC5
import qualified Data.SBV.Provers.DReal     as DReal
import qualified Data.SBV.Provers.MathSAT   as MathSAT
import qualified Data.SBV.Provers.Yices     as Yices
import qualified Data.SBV.Provers.Z3        as Z3
import qualified Data.SBV.Provers.OpenSMT   as OpenSMT

import GHC.TypeLits

mkConfig :: SMTSolver -> SMTLibVersion -> [Control.SMTOption] -> SMTConfig
mkConfig s smtVersion startOpts = SMTConfig { verbose                     = False
                                            , timing                      = NoTiming
                                            , printBase                   = 10
                                            , printRealPrec               = 16
                                            , crackNum                    = False
                                            , crackNumSurfaceVals         = []
                                            , transcript                  = Nothing
                                            , solver                      = s
                                            , smtLibVersion               = smtVersion
                                            , dsatPrecision               = Nothing
                                            , extraArgs                   = []
                                            , satCmd                      = "(check-sat)"
                                            , allSatTrackUFs              = True                   -- i.e., yes, do extract UI function values
                                            , allSatMaxModelCount         = Nothing                -- i.e., return all satisfying models
                                            , allSatPrintAlong            = False                  -- i.e., do not print models as they are found
                                            , isNonModelVar               = const False            -- i.e., everything is a model-variable by default
                                            , validateModel               = False
                                            , optimizeValidateConstraints = False
                                            , roundingMode                = RoundNearestTiesToEven
                                            , solverSetOptions            = startOpts
                                            , smtLib2Compliant            = True
                                            , ignoreExitCode              = False
                                            , redirectVerbose             = Nothing
                                            , firstifyUniqueLen           = 10
                                            , tpOptions                   = TPOptions { ribbonLength          = 40
                                                                                      , quiet                 = False
                                                                                      , printAsms             = False
                                                                                      , printStats            = False
                                                                                      , measuresBeingVerified = Set.empty
                                                                                      }
                                            }

-- | If supported, this makes all output go to stdout, which works better with SBV
-- Alas, not all solvers support it..
allOnStdOut :: Control.SMTOption
allOnStdOut = Control.DiagnosticOutputChannel "stdout"

-- | Default configuration for the ABC synthesis and verification tool.
abc :: SMTConfig
abc = mkConfig ABC.abc SMTLib2 [allOnStdOut]

-- | Default configuration for the Boolector SMT solver
boolector :: SMTConfig
boolector = mkConfig Boolector.boolector SMTLib2 []

-- | Default configuration for the Bitwuzla SMT solver
bitwuzla :: SMTConfig
bitwuzla = mkConfig Bitwuzla.bitwuzla SMTLib2 []

-- | Default configuration for the CVC4 SMT Solver.
cvc4 :: SMTConfig
cvc4 = mkConfig CVC4.cvc4 SMTLib2 [allOnStdOut]

-- | Default configuration for the CVC5 SMT Solver.
cvc5 :: SMTConfig
cvc5 = mkConfig CVC5.cvc5 SMTLib2 [allOnStdOut]

-- | Default configuration for the Yices SMT Solver.
dReal :: SMTConfig
dReal = mkConfig DReal.dReal SMTLib2 [ Control.OptionKeyword ":smtlib2_compliant" ["true"]
                                     ]

-- | Default configuration for the MathSAT SMT solver
mathSAT :: SMTConfig
mathSAT = mkConfig MathSAT.mathSAT SMTLib2 [allOnStdOut]

-- | Default configuration for the Yices SMT Solver.
yices :: SMTConfig
yices = mkConfig Yices.yices SMTLib2 []

-- | Default configuration for the Z3 SMT solver
z3 :: SMTConfig
z3 = mkConfig Z3.z3 SMTLib2 [ Control.OptionKeyword ":smtlib2_compliant" ["true"]
                            , allOnStdOut
                            ]

-- | Default configuration for the OpenSMT SMT solver
openSMT :: SMTConfig
openSMT = mkConfig OpenSMT.openSMT SMTLib2 [ Control.OptionKeyword ":smtlib2_compliant" ["true"]
                                           , allOnStdOut
                                           ]

-- | The default solver used by SBV. This is currently set to z3.
defaultSMTCfg :: SMTConfig
defaultSMTCfg = z3

-- | The default solver used by SBV for delta-satisfiability problems. This is currently set to dReal,
-- which is also the only solver that supports delta-satisfiability.
defaultDeltaSMTCfg :: SMTConfig
defaultDeltaSMTCfg = dReal

-- | A predicate is a symbolic program that returns a (symbolic) boolean value. For all intents and
-- purposes, it can be treated as an n-ary function from symbolic-values to a boolean. The 'Symbolic'
-- monad captures the underlying representation, and can/should be ignored by the users of the library,
-- unless you are building further utilities on top of SBV itself. Instead, simply use the 'Predicate'
-- type when necessary.
type Predicate = Symbolic SBool

-- | A constraint set is a symbolic program that returns no values. The idea is that the constraints/min-max
-- goals will serve as the collection of constraints that will be used for sat/optimize calls.
type ConstraintSet = Symbolic ()

-- | `Provable` is specialization of `ProvableM` to the `IO` monad. Unless you are using
-- transformers explicitly, this is the type you should prefer.
type Provable = ProvableM IO

-- | `Data.SBV.Provers.Satisfiable` is specialization of `SatisfiableM` to the `IO` monad. Unless you are using
-- transformers explicitly, this is the type you should prefer.
type Satisfiable = SatisfiableM IO

-- | A type @a@ is satisfiable if it has constraints, potentially returning a boolean. This class
-- captures essentially sat and optimize calls.
class ExtractIO m => SatisfiableM m a where
  -- | Reduce an arg, for sat purposes.
  satArgReduce :: a -> SymbolicT m SBool

  -- | Generalization of 'Data.SBV.sat'
  sat :: a -> m SatResult
  sat = satWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.satWith'
  satWith :: SMTConfig -> a -> m SatResult
  satWith cfg a = do r <- runWithQuery satArgReduce True (checkNoOptimizations >> Control.getSMTResult) cfg a
                     SatResult <$> if validationRequested cfg
                                   then validate satArgReduce True cfg a r
                                   else pure r

  -- | Generalization of 'Data.SBV.sat'
  dsat :: a -> m SatResult
  dsat = dsatWith defaultDeltaSMTCfg

  -- | Generalization of 'Data.SBV.satWith'
  dsatWith :: SMTConfig -> a -> m SatResult
  dsatWith cfg a = do r <- runWithQuery satArgReduce True (checkNoOptimizations >> Control.getSMTResult) cfg a
                      SatResult <$> if validationRequested cfg
                                    then validate satArgReduce True cfg a r
                                    else pure r

  -- | Generalization of 'Data.SBV.allSat'
  allSat :: a -> m AllSatResult
  allSat = allSatWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.allSatWith'
  allSatWith :: SMTConfig -> a -> m AllSatResult
  allSatWith cfg a = do asr <- runWithQuery satArgReduce True (checkNoOptimizations >> Control.getAllSatResult) cfg a
                        if validationRequested cfg
                           then do rs' <- mapM (validate satArgReduce True cfg a) (allSatResults asr)
                                   pure asr{allSatResults = rs'}
                           else pure asr

  -- | Generalization of 'Data.SBV.isSatisfiable'
  isSatisfiable :: a -> m Bool
  isSatisfiable = isSatisfiableWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.isSatisfiableWith'
  isSatisfiableWith :: SMTConfig -> a -> m Bool
  isSatisfiableWith cfg p = do r <- satWith cfg p
                               case r of
                                 SatResult Satisfiable{}   -> pure True
                                 SatResult Unsatisfiable{} -> pure False
                                 _                         -> error $ "SBV.isSatisfiable: Received: " ++ show r

  -- | Generalization of 'Data.SBV.optimize'
  optimize :: OptimizeStyle -> a -> m OptimizeResult
  optimize = optimizeWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.optimizeWith'
  optimizeWith :: SMTConfig -> OptimizeStyle -> a -> m OptimizeResult
  optimizeWith config style optGoal = do
                   res <- runWithQuery satArgReduce True opt config optGoal
                   if not (optimizeValidateConstraints config)
                      then pure res
                      else let v :: SMTResult -> m SMTResult
                               v = validate satArgReduce True config optGoal
                           in case res of
                                LexicographicResult m -> LexicographicResult <$> v m
                                IndependentResult xs  -> let w []            sofar = pure (reverse sofar)
                                                             w ((n, m):rest) sofar = v m >>= \m' -> w rest ((n, m') : sofar)
                                                         in IndependentResult <$> w xs []
                                ParetoResult (b, rs)  -> ParetoResult . (b, ) <$> mapM v rs

    where opt = do mbDirs <- Control.startOptimizer config style

                   case mbDirs of
                     Nothing   -> error $ unlines [ ""
                                                  , "*** Data.SBV: Unsupported call to optimize when no objectives are present."
                                                  , "*** Use \"sat\" for plain satisfaction"
                                                  ]
                     Just (objectives, optimizerDirectives) -> do
                       mapM_ (Control.send True . T.pack) optimizerDirectives

                       case style of
                         Lexicographic -> LexicographicResult <$> Control.getLexicographicOptResults
                         Independent   -> IndependentResult   <$> Control.getIndependentOptResults (map objectiveName objectives)
                         Pareto mbN    -> ParetoResult        <$> Control.getParetoOptResults mbN

-- | Find a satisfying assignment to a property with multiple solvers, running them in separate threads. The
-- results will be returned in the order produced.
satWithAll :: Satisfiable a => [SMTConfig] -> a -> IO [(Solver, NominalDiffTime, SatResult)]
satWithAll = (`sbvWithAll` satWith)

-- | Find a satisfying assignment to a property with multiple solvers, running them in separate threads. Only
-- the result of the first one to finish will be returned, remaining threads will be killed.
-- Note that we send an exception to the losing processes, but we do *not* actually wait for them
-- to finish. In rare cases this can lead to zombie processes. In previous experiments, we found
-- that some processes take their time to terminate. So, this solution favors quick turnaround.
satWithAny :: Satisfiable a => [SMTConfig] -> a -> IO (Solver, NominalDiffTime, SatResult)
satWithAny = (`sbvWithAny` satWith)

-- | Find a satisfying assignment to a property using a single solver, but
-- providing several query problems of interest, with each query running in a
-- separate thread and return the first one that returns. This can be useful to
-- use symbolic mode to drive to a location in the search space of the solver
-- and then refine the problem in query mode. If the computation is very hard to
-- solve for the solver than running in concurrent mode may provide a large
-- performance benefit.
satConcurrentWithAny :: Satisfiable a => SMTConfig -> [Query b] -> a -> IO (Solver, NominalDiffTime, SatResult)
satConcurrentWithAny solver qs a = do (slvr,time,result) <- sbvConcurrentWithAny solver go qs a
                                      pure (slvr, time, SatResult result)
  where go cfg a' q = runWithQuery satArgReduce True (do _ <- q; checkNoOptimizations >> Control.getSMTResult) cfg a'

-- | Find a satisfying assignment to a property using a single solver, but run
-- each query problem in a separate isolated thread and wait for each thread to
-- finish. See 'satConcurrentWithAny' for more details.
satConcurrentWithAll :: Satisfiable a => SMTConfig -> [Query b] -> a -> IO [(Solver, NominalDiffTime, SatResult)]
satConcurrentWithAll solver qs a = do results <- sbvConcurrentWithAll solver go qs a
                                      pure $ (\(a',b,c) -> (a',b,SatResult c)) <$> results
  where go cfg a' q = runWithQuery satArgReduce True (do _ <- q; checkNoOptimizations >> Control.getSMTResult) cfg a'

-- | A type @a@ is provable if we can turn it into a predicate, i.e., it has to return a boolean.
-- This class captures essentially prove calls.
class ExtractIO m => ProvableM m a where
  -- | Reduce an arg, for proof purposes.
  proofArgReduce :: a -> SymbolicT m SBool

  -- | Generalization of 'Data.SBV.prove'
  prove :: a -> m ThmResult
  prove = proveWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.proveWith'
  proveWith :: SMTConfig -> a -> m ThmResult
  proveWith cfg a = do r <- runWithQuery proofArgReduce False (checkNoOptimizations >> Control.getSMTResult) cfg a
                       ThmResult <$> if validationRequested cfg
                                     then validate proofArgReduce False cfg a r
                                     else pure r

  -- | Generalization of 'Data.SBV.dprove'
  dprove :: a -> m ThmResult
  dprove = dproveWith defaultDeltaSMTCfg

  -- | Generalization of 'Data.SBV.dproveWith'
  dproveWith :: SMTConfig -> a -> m ThmResult
  dproveWith cfg a = do r <- runWithQuery proofArgReduce False (checkNoOptimizations >> Control.getSMTResult) cfg a
                        ThmResult <$> if validationRequested cfg
                                      then validate proofArgReduce False cfg a r
                                      else pure r

  -- | Generalization of 'Data.SBV.isVacuousProof'
  isVacuousProof :: a -> m Bool
  isVacuousProof = isVacuousProofWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.isVacuousProofWith'
  isVacuousProofWith :: SMTConfig -> a -> m Bool
  isVacuousProofWith cfg a = -- NB. Can't call runWithQuery since last constraint would become the implication!
       fst <$> runSymbolic cfg (SMTMode QueryInternal ISetup True cfg) (proofArgReduce a >> Control.executeQuery QueryInternal check)
     where
       check = do cs <- Control.checkSat
                  case cs of
                    Control.Unsat  -> pure True
                    Control.Sat    -> pure False
                    Control.DSat{} -> pure False
                    Control.Unk    -> error "SBV: isVacuous: Solver returned unknown!"

  -- | Generalization of 'Data.SBV.isTheorem'
  isTheorem :: a -> m Bool
  isTheorem = isTheoremWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.isTheoremWith'
  isTheoremWith :: SMTConfig -> a -> m Bool
  isTheoremWith cfg p = do r <- proveWith cfg p
                           let bad = error $ "SBV.isTheorem: Received:\n" ++ show r
                           case r of
                             ThmResult Unsatisfiable{} -> pure True
                             ThmResult Satisfiable{}   -> pure False
                             ThmResult DeltaSat{}      -> pure False
                             ThmResult SatExtField{}   -> pure False
                             ThmResult Unknown{}       -> bad
                             ThmResult ProofError{}    -> bad

-- | Prove a property with multiple solvers, running them in separate threads. Only
-- the result of the first one to finish will be returned, remaining threads will be killed.
-- Note that we send an exception to the losing processes, but we do *not* actually wait for them
-- to finish. In rare cases this can lead to zombie processes. In previous experiments, we found
-- that some processes take their time to terminate. So, this solution favors quick turnaround.
proveWithAny :: Provable a => [SMTConfig] -> a -> IO (Solver, NominalDiffTime, ThmResult)
proveWithAny  = (`sbvWithAny` proveWith)

-- | Prove a property with multiple solvers, running them in separate threads. The
-- results will be returned in the order produced.
proveWithAll :: Provable a => [SMTConfig] -> a -> IO [(Solver, NominalDiffTime, ThmResult)]
proveWithAll  = (`sbvWithAll` proveWith)

-- | Prove a property by running many queries each isolated to their own thread
-- concurrently and return the first that finishes, killing the others
proveConcurrentWithAny :: Provable a => SMTConfig -> [Query b] -> a -> IO (Solver, NominalDiffTime, ThmResult)
proveConcurrentWithAny solver qs a = do (slvr,time,result) <- sbvConcurrentWithAny solver go qs a
                                        pure (slvr, time, ThmResult result)
  where go cfg a' q = runWithQuery proofArgReduce False (do _ <- q;  checkNoOptimizations >> Control.getSMTResult) cfg a'

-- | Prove a property by running many queries each isolated to their own thread
-- concurrently and wait for each to finish returning all results
proveConcurrentWithAll :: Provable a => SMTConfig -> [Query b] -> a -> IO [(Solver, NominalDiffTime, ThmResult)]
proveConcurrentWithAll solver qs a = do results <- sbvConcurrentWithAll solver go qs a
                                        pure $ (\(a',b,c) -> (a',b,ThmResult c)) <$> results
  where go cfg a' q = runWithQuery proofArgReduce False (do _ <- q; checkNoOptimizations >> Control.getSMTResult) cfg a'

-- | Validate a model obtained from the solver
validate :: MonadIO m => (a -> SymbolicT m SBool) -> Bool -> SMTConfig -> a -> SMTResult -> m SMTResult
validate reducer isSAT cfg p res =
     case res of
       Unsatisfiable{} -> pure res
       Satisfiable _ m -> case modelBindings m of
                            Nothing  -> error "Data.SBV.validate: Impossible happened; no bindings generated during model validation."
                            Just env -> check env

       DeltaSat {}     -> cant [ "The model is delta-satisfiable."
                               , "Cannot validate delta-satisfiable models."
                               ]

       SatExtField{}   -> cant [ "The model requires an extension field value."
                               , "Cannot validate models with infinities/epsilons produced during optimization."
                               , ""
                               , "To turn validation off, use `cfg{optimizeValidateConstraints = False}`"
                               ]

       Unknown{}       -> pure res
       ProofError{}    -> pure res

  where cant msg = pure $ ProofError cfg (msg ++ [ ""
                                                   , "Unable to validate the produced model."
                                                   ]) (Just res)

        -- Values of uninterpreted constants/functions in the model
        uiEnv = case res of
                  Satisfiable _ m -> fromMaybe [] (modelUIBindings m)
                  _               -> []

        check env = do let envShown = showModelDictionary True True cfg modelBinds
                              where modelBinds = [(T.unpack n, RegularCV v) | (NamedSymVar _ n, v) <- env]

                           notify s
                             | not (verbose cfg) = pure ()
                             | True              = debug cfg ["[VALIDATE] " `alignPlain` T.pack s]

                       notify $ "Validating the model. " ++ if null env then "There are no assignments." else "Assignment:"
                       mapM_ notify ["    " ++ l | l <- lines envShown]

                       result <- snd <$> runSymbolic cfg (Concrete (Just (isSAT, env))) (reducer p >>= output)

                       let -- Values that remained symbolic in the concrete run, but can be computed using
                           -- the model values of uninterpreted constants and functions
                           residual = evalResidual uiEnv result

                           -- Boolean value of an SV, if we can compute it
                           valueOf sv
                             | sv == trueSV  = Just True
                             | sv == falseSV = Just False
                             | True          = cvToBool <$> sv `Map.lookup` residual

                           explain  = [ ""
                                      , "Assignment:"  ++ if null env then " <none>" else ""
                                      ]
                                   ++ [ ""          | not (null env)]
                                   ++ [ "    " ++ l | l <- lines envShown]
                                   ++ [ "" ]

                           wrap tag extras = pure $ ProofError cfg (tag : explain ++ extras) (Just res)

                           giveUp   s     = wrap ("Data.SBV: Cannot validate the model: " ++ s)
                                                 [ "SBV's model validator is incomplete, and cannot handle this particular case."
                                                 , "Please report this as a feature request or possibly a bug!"
                                                 ]

                           badModel s     = wrap ("Data.SBV: Model validation failure: " ++ s)
                                                 [ "Backend solver returned a model that does not satisfy the constraints."
                                                 , "This could indicate a bug in the backend solver, or SBV itself. Please report."
                                                 ]

                           notConcrete sv = wrap ("Data.SBV: Cannot validate the model, since " ++ show sv ++ " is not concretely computable.")
                                                 (  perhaps (explainResidual uiEnv result residual sv)
                                                 )
                                where perhaps Nothing  = case resObservables result of
                                                           [] -> []
                                                           xs -> [ "There are observable values in the model: " ++ unwords [show n | (n, _, _) <- xs]
                                                                 , "SBV cannot validate in the presence of observables, unfortunately."
                                                                 , "Try validation after removing calls to 'observe'."
                                                                 ]

                                      perhaps (Just x) = [ x
                                                         , ""
                                                         , "SBV's model validator is incomplete, and cannot handle this particular case."
                                                         , "Please report this as a feature request or possibly a bug!"
                                                         ]

                           cstrs = S.toList $ resConstraints result

                           walkConstraints [] cont = do
                              unless (null cstrs) $ notify "Validated all constraints."
                              cont
                           walkConstraints ((isSoft, attrs, sv) : rest) cont
                              | kindOf sv /= KBool
                              = giveUp $ "Constraint tied to " ++ show sv ++ " is non-boolean."
                              | isSoft || valueOf sv == Just True
                              = walkConstraints rest cont
                              | valueOf sv == Just False
                              = case mbName of
                                  Just nm -> badModel $ "Named constraint " ++ show nm ++ " evaluated to False."
                                  Nothing -> badModel "A constraint was violated."
                              | True
                              = notConcrete sv
                              where mbName = listToMaybe [n | (":named", n) <- attrs]

                           -- SAT: All outputs must be true
                           satLoop []
                             = do notify "All outputs are satisfied. Validation complete."
                                  pure res
                           satLoop (sv:svs)
                             | kindOf sv /= KBool
                             = giveUp $ "Output tied to " ++ show sv ++ " is non-boolean."
                             | valueOf sv == Just True
                             = satLoop svs
                             | valueOf sv == Just False
                             = badModel "Final output evaluated to False."
                             | True
                             = notConcrete sv

                           -- Proof: At least one output must be false
                           proveLoop [] somethingFailed
                             | somethingFailed = do notify "Counterexample is validated."
                                                    pure res
                             | True            = do notify "Counterexample violates none of the outputs."
                                                    badModel "Counter-example violates no constraints."
                           proveLoop (sv:svs) somethingFailed
                             | kindOf sv /= KBool
                             = giveUp $ "Output tied to " ++ show sv ++ " is non-boolean."
                             | valueOf sv == Just True
                             = proveLoop svs somethingFailed
                             | valueOf sv == Just False
                             = proveLoop svs True
                             | True
                             = notConcrete sv

                           -- Output checking is tricky, since we behave differently for different modes
                           checkOutputs []
                             | null cstrs
                             = giveUp "Impossible happened: There are no outputs nor any constraints to check."
                           checkOutputs os
                             = do notify "Validating outputs."
                                  if isSAT then satLoop   os
                                           else proveLoop os False

                       notify $ if null cstrs
                                then "There are no constraints to check."
                                else "Validating " ++ show (length cstrs) ++ " constraint(s)."

                       walkConstraints cstrs (checkOutputs (resOutputs result))

-- | Values of uninterpreted constants and functions in a model, as used during validation.
type UIEnv = [(String, Either String ([([CV], CV)], CV))]

-- | Find the model value of an uninterpreted constant/function.
lookupUI :: UIEnv -> T.Text -> Maybe (Either String ([([CV], CV)], CV))
lookupUI uis f = unBar (T.unpack f) `lookup` [(unBar n, v) | (n, v) <- uis]

-- | After the concrete run of model validation, some values remain symbolic if they depend on
-- uninterpreted constants or functions. Evaluate them using the values of the uninterpreted
-- values in the model. We return all the values we can compute.
evalResidual :: UIEnv -> Result -> Map.Map SV CV
evalResidual uis result = S.foldl' step initial (pgmAssignments (resAsgns result))
  where initial = Map.fromList $ (trueSV, trueCV) : (falseSV, falseCV) : snd (resConsts result)

        step known (sv, SBVApp op args) = maybe known (\cv -> Map.insert sv cv known) (evalNode known (kindOf sv) op args)

        evalNode known k op args
          -- For ite, we only need the value of the branch taken
          | Ite <- op, [c, t, e] <- args
          = do b <- cvToBool <$> c `Map.lookup` known
               (if b then t else e) `Map.lookup` known
          -- Short-cut and/or. Note that these are also used for bit-vectors, where we can't short-cut.
          | And <- op, k == KBool, any (has False) args = Just falseCV
          | Or  <- op, k == KBool, any (has True)  args = Just trueCV
          | True                                        = mapM (`Map.lookup` known) args >>= evalOp uis k op
          where has b a = (cvToBool <$> a `Map.lookup` known) == Just b

-- | Evaluate an operation on concrete arguments, using the model values of uninterpreted
-- constants and functions. Returns 'Nothing' if we cannot.
evalOp :: UIEnv -> Kind -> Op -> [CV] -> Maybe CV
evalOp uis k op args = case (op, args) of
    (Uninterpreted f, _) -> case lookupUI uis f of
                              Just (Right (tbl, def)) -> lookupFirst args tbl def
                              _                       -> Nothing

    (Label _, [a]) -> Just a

    (TupleConstructor _, _)               -> Just $ CV k (CTuple (map cvVal args))
    (TupleAccess i _, [CV _ (CTuple vs)])
       | i >= 1, i <= length vs           -> Just $ CV k (vs !! (i-1))

    (ADTOp (ADTConstructor c _), _)                  -> Just $ CV k (CADT (T.unpack c, [(kindOf a, cvVal a) | a <- args]))
    (ADTOp (ADTTester t _),      [CV _ (CADT (c, _))]) -> Just $ if T.unpack t == "is-" ++ c then trueCV else falseCV
    (ADTOp (ADTAccessor a _),    [CV _ (CADT (c, fs))])
       | Just i <- accessorIndex c (T.unpack a), i >= 1, i <= length fs
       -> Just $ CV k (snd (fs !! (i-1)))

    (SeqOp (SeqNth _), [CV _ (CList xs), CV _ (CInteger i)])
       | i >= 0, i < genericLength xs -> Just $ CV k (xs `genericIndex` i)

    (ReadArray,  [CV (KArray ki _) (CArray (ArrayModel tbl def)), i])
       -> CV k <$> lookupFirst [i] [([CV ki key], v) | (key, v) <- tbl] def
    (WriteArray, [CV _ (CArray (ArrayModel tbl def)), i, v]) -> Just $ CV k $ CArray $ ArrayModel ((cvVal i, cvVal v) : tbl) def

    _ -> case (op, map lit args) of
           (Plus,          [a, b])    -> conc $ svPlus        a b
           (Times,         [a, b])    -> conc $ svTimes       a b
           (Minus,         [a, b])    -> conc $ svMinus       a b
           (UNeg,          [a])       -> conc $ svUNeg        a
           (Abs,           [a])       -> conc $ svAbs         a
           (Quot,          [a, b])    -> conc $ svQuot        a b
           (Rem,           [a, b])    -> conc $ svRem         a b
           (Equal True,    [a, b])    -> conc $ svStrongEqual a b
           (Equal False,   [a, b])    -> conc $ svEqual       a b
           (NotEqual,      [a, b])    -> conc $ svNotEqual    a b
           (LessThan,      [a, b])    -> conc $ svLessThan    a b
           (GreaterThan,   [a, b])    -> conc $ svGreaterThan a b
           (LessEq,        [a, b])    -> conc $ svLessEq      a b
           (GreaterEq,     [a, b])    -> conc $ svGreaterEq   a b
           (Implies,       [a, b])    -> conc $ svImplies     a b
           (And,           [a, b])    -> conc $ svAnd         a b
           (Or,            [a, b])    -> conc $ svOr          a b
           (XOr,           [a, b])    -> conc $ svXOr         a b
           (Not,           [a])       -> conc $ svNot         a
           (Shl,           [a, b])    -> conc $ svShiftLeft   a b
           (Shr,           [a, b])    -> conc $ svShiftRight  a b
           (Rol i,         [a])       -> conc $ svRol         a i
           (Ror i,         [a])       -> conc $ svRor         a i
           (Divides n,     [a])       -> conc $ svDivides     n a
           (Extract i j,   [a])       -> conc $ svExtract     i j a
           (Join,          [a, b])    -> conc $ svJoin        a b
           (ZeroExtend i,  [a])       -> conc $ svZeroExtend  i a
           (SignExtend i,  [a])       -> conc $ svSignExtend  i a
           (KindCast f t,  [a])
             | all isIntegral [f, t]  -> conc $ svFromIntegral t a

           (OverflowOp o', [a])       -> conc $ svMkOverflow1 o' a
           (OverflowOp o', [a, b])    -> conc $ svMkOverflow2 o' a b

           (IEEEFP fop,    largs)     -> case (fop, largs) of
                                           (FP_Abs,             [a])           -> conc $ svFPAbs             a
                                           (FP_Neg,             [a])           -> conc $ svFPNeg             a
                                           (FP_Add,             [rm, a, b])    -> conc $ svFPAdd             rm a b
                                           (FP_Sub,             [rm, a, b])    -> conc $ svFPSub             rm a b
                                           (FP_Mul,             [rm, a, b])    -> conc $ svFPMul             rm a b
                                           (FP_Div,             [rm, a, b])    -> conc $ svFPDiv             rm a b
                                           (FP_FMA,             [rm, a, b, c]) -> conc $ svFPFMA             rm a b c
                                           (FP_Sqrt,            [rm, a])       -> conc $ svFPSqrt            rm a
                                           (FP_Rem,             [a, b])        -> conc $ svFPRem             a b
                                           (FP_RoundToIntegral, [rm, a])       -> conc $ svFPRoundToIntegral rm a
                                           (FP_Min,             [a, b])        -> conc $ svFPMin             a b
                                           (FP_Max,             [a, b])        -> conc $ svFPMax             a b
                                           (FP_ObjEqual,        [a, b])        -> conc $ svStrongEqual       a b
                                           (FP_IsNormal,        [a])           -> conc $ svFPIsNormal        a
                                           (FP_IsSubnormal,     [a])           -> conc $ svFPIsSubnormal     a
                                           (FP_IsZero,          [a])           -> conc $ svFPIsZero          a
                                           (FP_IsInfinite,      [a])           -> conc $ svFPIsInfinite      a
                                           (FP_IsNaN,           [a])           -> conc $ svFPIsNaN           a
                                           (FP_IsNegative,      [a])           -> conc $ svFPIsNegative      a
                                           (FP_IsPositive,      [a])           -> conc $ svFPIsPositive      a
                                           _                                   -> Nothing
           _                          -> Nothing
  where lit a = SVal (kindOf a) (Left a)

        conc (SVal _ (Left c)) = Just c
        conc _                 = Nothing

        isIntegral x = isBounded x || isUnbounded x

-- | Look up a key in a table, where earlier entries take precedence, returning the default if there's no match.
-- Keys are compared using object equality, which can't be done structurally: The same value can have different
-- representations, as is the case for arrays. If we can't decide whether an entry matches before we find a
-- match, we return 'Nothing'.
lookupFirst :: [CV] -> [([CV], a)] -> a -> Maybe a
lookupFirst key tbl def = go tbl
  where go []              = Just def
        go ((k, v) : rest) = case zipWith same key k of
                               eqs | Just False `elem` eqs   -> go rest
                                   | all (== Just True)  eqs -> Just v
                                   | True                    -> Nothing

        same a b = case svStrongEqual (SVal (kindOf a) (Left a)) (SVal (kindOf b) (Left b)) of
                     SVal _ (Left r) -> Just (cvToBool r)
                     _               -> Nothing

-- | Given a constructor name and an accessor name, find which field the accessor
-- refers to, if the accessor belongs to this constructor. Accessors are named @get<Constructor>_<i>@.
accessorIndex :: String -> String -> Maybe Int
accessorIndex c a = stripPrefix ("get" ++ c ++ "_") a >>= readMaybe

-- | Explain why an SV couldn't be computed during validation, by finding the operation responsible.
-- This is incomplete, but should capture the most common cases.
explainResidual :: UIEnv -> Result -> Map.Map SV CV -> SV -> Maybe String
explainResidual uis result known = go
  where defs    = Map.fromList $ S.toList $ pgmAssignments (resAsgns result)
        defined = [unBar d | (d, _) <- resDefinitions result]

        go sv = case sv `Map.lookup` defs of
                  Nothing            -> Nothing
                  Just (SBVApp o as)
                    -- Follow the branch taken in an ite
                    | Ite <- o, [c, t, e] <- as, Just b <- cvToBool <$> c `Map.lookup` known
                    -> go (if b then t else e)
                    -- If an argument is not known, the problem is further down
                    | unknowns@(_:_) <- [a | a <- as, a `Map.notMember` known]
                    -> case mapMaybe go unknowns of
                         r : _ -> Just r
                         []    -> Just $ describe o Nothing
                    | True
                    -> Just $ describe o (mapM (`Map.lookup` known) as)

        isIrrational (CV _ (CAlgReal r)) = not (isExactRational r)
        isIrrational _                   = False

        unspecified = "This value is not specified by SMTLib, and SBV cannot determine what the solver picked for it."

        describe o mbArgs = case (o, mbArgs) of
          (QuantifiedBool{},     _) -> "The value depends on a quantified variable."
          (IEEEFP _,             _) -> "Not all floating point operations are supported concretely."
          (SpecialRelOp{},       _) -> "Special relations are not supported concretely."
          (ArrayInit (Right _),  _) -> "Arrays created via lambdaArray are not supported concretely."

          (_, Just cvs) | any isIrrational cvs
             -> "The value depends on an irrational algebraic real, which SBV cannot compute with concretely."

          (ADTOp (ADTAccessor a _), Just [CV _ (CADT (c, _))])
             -> unwords [ "The field accessor", T.unpack a, "is applied to a value built with the constructor", c ++ "."
                        , unspecified
                        ]

          (SeqOp (SeqNth _), Just [CV _ (CList xs), CV _ (CInteger i)])
             -> unwords [ "Element", show i, "of a list of length", show (length xs), "is accessed."
                        , unspecified
                        ]

          (Uninterpreted f, _)
             | unBar (T.unpack f) `elem` defined
             -> "The function " ++ unBar (T.unpack f) ++ " is applied to arguments that depend on uninterpreted values. SBV cannot evaluate it."
             | True
             -> case (lookupUI uis f, mbArgs) of
                  (Nothing,      _)      -> "The model has no value for the uninterpreted name " ++ unBar (T.unpack f) ++ "."
                  (Just Left{},  _)      -> "The model value for the uninterpreted function " ++ unBar (T.unpack f) ++ " is too complicated for SBV to evaluate."
                  (Just Right{}, Just _) -> "SBV cannot decide which entry in the model value for the uninterpreted function " ++ unBar (T.unpack f) ++ " applies to its arguments."
                  (Just Right{}, _)      -> "The uninterpreted function " ++ unBar (T.unpack f) ++ " is applied to arguments that are not concretely computable."

          (ReadArray, Just _) -> "SBV cannot decide which entry of the array applies to the index it is read at."

          _ -> "SBV cannot concretely evaluate the operation: " ++ show o

-- | Given a satisfiability problem, extract the function definitions in it
defs2smt :: SatisfiableM m a => a -> m String
defs2smt = generateSMTBenchMarkGen True satArgReduce defs
  where defs (SMTLibPgm _ _ ds) = T.unpack ds

-- | Create an SMT-Lib2 benchmark, for a SAT query.
generateSMTBenchmarkSat :: SatisfiableM m a => a -> m String
generateSMTBenchmarkSat = generateSMTBenchMarkGen True satArgReduce (\p -> show p ++ "\n(check-sat)\n")

-- | Create an SMT-Lib2 benchmark, for a Proof query.
generateSMTBenchmarkProof :: ProvableM m a => a -> m String
generateSMTBenchmarkProof = generateSMTBenchMarkGen False proofArgReduce (\p -> show p ++ "\n(check-sat)\n")

-- | Generic benchmark creator
generateSMTBenchMarkGen :: MonadIO m => Bool -> (a -> SymbolicT m SBool) -> (SMTLibPgm -> b) -> a -> m b
generateSMTBenchMarkGen isSat reduce render a = do
      t <- liftIO getZonedTime

      let comments = ["Automatically created by SBV on " ++ show t]
          cfg      = defaultSMTCfg { smtLibVersion = SMTLib2 }

      (_, res) <- runSymbolic cfg (SMTMode QueryInternal ISetup isSat cfg) $ reduce a >>= output

      let SMTProblem{smtLibPgm} = Control.runProofOn (SMTMode QueryInternal IRun isSat cfg) QueryInternal comments res

      pure $ render (smtLibPgm cfg)

checkNoOptimizations :: MonadIO m => QueryT m ()
checkNoOptimizations = do objectives <- Control.getObjectives

                          unless (null objectives) $
                                error $ unlines [ ""
                                                , "*** Data.SBV: Unsupported call sat/prove when optimization objectives are present."
                                                , "*** Use \"optimize\"/\"optimizeWith\" to calculate optimal satisfaction!"
                                                ]

instance ExtractIO m => SatisfiableM m (SymbolicT m ()) where satArgReduce a = satArgReduce ((a >> pure sTrue) :: SymbolicT m SBool)
-- instance ExtractIO m => ProvableM m (SymbolicT m ())  -- NO INSTANCE ON PURPOSE; don't want to prove goals

instance ExtractIO m => SatisfiableM m (SymbolicT m SBool) where satArgReduce   = id
instance ExtractIO m => ProvableM    m (SymbolicT m SBool) where proofArgReduce = id

instance ExtractIO m => SatisfiableM m SBool where satArgReduce   = pure
instance ExtractIO m => ProvableM    m SBool where proofArgReduce = pure

instance {-# OVERLAPPABLE #-} (ExtractIO m, SatisfiableM m a) => SatisfiableM m (SymbolicT m a) where satArgReduce   a = a >>= satArgReduce
instance {-# OVERLAPPABLE #-} (ExtractIO m, ProvableM    m a) => ProvableM    m (SymbolicT m a) where proofArgReduce a = a >>= proofArgReduce

instance (ExtractIO m, SymVal a, Constraint Symbolic r, SatisfiableM m r) => SatisfiableM m (Forall nm a -> r) where
  satArgReduce = satArgReduce . quantifiedBool

instance (ExtractIO m, SymVal a, Constraint Symbolic r, ProvableM m r) => ProvableM m (Forall nm a -> r) where
  proofArgReduce = proofArgReduce . quantifiedBool

instance (ExtractIO m, SymVal a, Constraint Symbolic r, SatisfiableM m r) => SatisfiableM m (Exists nm a -> r) where
  satArgReduce = satArgReduce . quantifiedBool

instance (ExtractIO m, SymVal a, Constraint Symbolic r, SatisfiableM m r, EqSymbolic (SBV a)) => SatisfiableM m (ExistsUnique nm a -> r) where
  satArgReduce = satArgReduce . quantifiedBool

instance (KnownNat n, ExtractIO m, SymVal a, Constraint Symbolic r, ProvableM m r) => ProvableM m (ForallN n nm a -> r) where
  proofArgReduce = proofArgReduce . quantifiedBool

instance (KnownNat n, ExtractIO m, SymVal a, Constraint Symbolic r, SatisfiableM m r) => SatisfiableM m (ExistsN n nm a -> r) where
  satArgReduce = satArgReduce . quantifiedBool

instance (ExtractIO m, SymVal a, Constraint Symbolic r, ProvableM m r) => ProvableM m (Exists nm a -> r) where
  proofArgReduce = proofArgReduce . quantifiedBool

instance (ExtractIO m, SymVal a, Constraint Symbolic r, ProvableM m r, EqSymbolic (SBV a)) => ProvableM m (ExistsUnique nm a -> r) where
  proofArgReduce = proofArgReduce . quantifiedBool

instance (KnownNat n, ExtractIO m, SymVal a, Constraint Symbolic r, SatisfiableM m r) => SatisfiableM m (ForallN n nm a -> r) where
  satArgReduce = satArgReduce . quantifiedBool

instance (KnownNat n, ExtractIO m, SymVal a, Constraint Symbolic r, ProvableM m r) => ProvableM m (ExistsN n nm a -> r) where
  proofArgReduce = proofArgReduce . quantifiedBool

{-
-- The following is a possible definition, but it lets us write properties that
-- are not useful.. Such as: prove $ \x y -> (x::SInt8) == y
-- Running that will throw an exception since Haskell's equality is not be supported by symbolic things. (Needs .==).
-- So, we avoid these instances.
instance ExtractIO m => ProvableM m Bool where
  proofArgReduce x  = proofArgReduce (if x then sTrue else sFalse :: SBool)

instance ExtractIO m => SatisfiableM m Bool where
  satArgReduce x  = satArgReduce (if x then sTrue else sFalse :: SBool)
-}

-- | Create an argument
mkArg :: (SymVal a, MonadSymbolic m) => m (SBV a)
mkArg = mkSymVal (NonQueryVar Nothing) Nothing

-- Functions
instance (SymVal a, SatisfiableM m p) => SatisfiableM m (SBV a -> p) where
  satArgReduce fn = mkArg >>= \a -> satArgReduce $ fn a

instance (SymVal a, ProvableM m p) => ProvableM m (SBV a -> p) where
  proofArgReduce fn = mkArg >>= \a -> proofArgReduce $ fn a

-- | Create an 'SBVs' sequence of arguments
mkArgs :: MonadSymbolic m => SymValInsts as -> m (SBVs as)
mkArgs SymValsNil = pure SBVsNil
mkArgs (SymValsCons insts) = SBVsCons <$> mkArgs insts <*> mkArg

-- Multi-arity Functions
instance (SymVals as, SatisfiableM m p) => SatisfiableM m (SBVs as -> p) where
  satArgReduce fn = mkArgs symValInsts >>= \args -> satArgReduce $ fn args

instance (SymVals as, ProvableM m p) => ProvableM m (SBVs as -> p) where
  proofArgReduce fn = mkArgs symValInsts >>= \args -> proofArgReduce $ fn args

-- 2 Tuple
instance (SymVal a, SymVal b, SatisfiableM m p) => SatisfiableM m ((SBV a, SBV b) -> p) where
  satArgReduce fn = mkArg >>= \a -> satArgReduce $ \b -> fn (a, b)

instance (SymVal a, SymVal b, ProvableM m p) => ProvableM m ((SBV a, SBV b) -> p) where
  proofArgReduce fn = mkArg >>= \a -> proofArgReduce $ \b -> fn (a, b)

-- 3 Tuple
instance (SymVal a, SymVal b, SymVal c, SatisfiableM m p) => SatisfiableM m ((SBV a, SBV b, SBV c) -> p) where
  satArgReduce fn = mkArg >>= \a -> satArgReduce $ \b c -> fn (a, b, c)

instance (SymVal a, SymVal b, SymVal c, ProvableM m p) => ProvableM m ((SBV a, SBV b, SBV c) -> p) where
  proofArgReduce fn = mkArg >>= \a -> proofArgReduce $ \b c -> fn (a, b, c)

-- 4 Tuple
instance (SymVal a, SymVal b, SymVal c, SymVal d, SatisfiableM m p) => SatisfiableM m ((SBV a, SBV b, SBV c, SBV d) -> p) where
  satArgReduce fn = mkArg  >>= \a -> satArgReduce $ \b c d -> fn (a, b, c, d)

instance (SymVal a, SymVal b, SymVal c, SymVal d, ProvableM m p) => ProvableM m ((SBV a, SBV b, SBV c, SBV d) -> p) where
  proofArgReduce fn = mkArg  >>= \a -> proofArgReduce $ \b c d -> fn (a, b, c, d)

-- 5 Tuple
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SatisfiableM m p) => SatisfiableM m ((SBV a, SBV b, SBV c, SBV d, SBV e) -> p) where
  satArgReduce fn = mkArg >>= \a -> satArgReduce $ \b c d e -> fn (a, b, c, d, e)

instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, ProvableM m p) => ProvableM m ((SBV a, SBV b, SBV c, SBV d, SBV e) -> p) where
  proofArgReduce fn = mkArg >>= \a -> proofArgReduce $ \b c d e -> fn (a, b, c, d, e)

-- 6 Tuple
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SatisfiableM m p) => SatisfiableM m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> p) where
  satArgReduce fn = mkArg >>= \a -> satArgReduce $ \b c d e f -> fn (a, b, c, d, e, f)

instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, ProvableM m p) => ProvableM m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> p) where
  proofArgReduce fn = mkArg >>= \a -> proofArgReduce $ \b c d e f -> fn (a, b, c, d, e, f)

-- 7 Tuple
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, SatisfiableM m p) => SatisfiableM m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> p) where
  satArgReduce fn = mkArg >>= \a -> satArgReduce $ \b c d e f g -> fn (a, b, c, d, e, f, g)

instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, ProvableM m p) => ProvableM m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> p) where
  proofArgReduce fn = mkArg >>= \a -> proofArgReduce $ \b c d e f g -> fn (a, b, c, d, e, f, g)

-- 8 Tuple
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, SymVal h, SatisfiableM m p) => SatisfiableM m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g, SBV h) -> p) where
  satArgReduce fn = mkArg >>= \a -> satArgReduce $ \b c d e f g h -> fn (a, b, c, d, e, f, g, h)

instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, SymVal h, ProvableM m p) => ProvableM m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g, SBV h) -> p) where
  proofArgReduce fn = mkArg >>= \a -> proofArgReduce $ \b c d e f g h -> fn (a, b, c, d, e, f, g, h)

-- 9 Tuple
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, SymVal h, SymVal i, SatisfiableM m p) => SatisfiableM m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g, SBV h, SBV i) -> p) where
  satArgReduce fn = mkArg >>= \a -> satArgReduce $ \b c d e f g h i -> fn (a, b, c, d, e, f, g, h, i)

instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, SymVal h, SymVal i, ProvableM m p) => ProvableM m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g, SBV h, SBV i) -> p) where
  proofArgReduce fn = mkArg >>= \a -> proofArgReduce $ \b c d e f g h i -> fn (a, b, c, d, e, f, g, h, i)

-- 10 Tuple
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, SymVal h, SymVal i, SymVal j, SatisfiableM m p) => SatisfiableM m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g, SBV h, SBV i, SBV j) -> p) where
  satArgReduce fn = mkArg >>= \a -> satArgReduce $ \b c d e f g h i j -> fn (a, b, c, d, e, f, g, h, i, j)

instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, SymVal h, SymVal i, SymVal j, ProvableM m p) => ProvableM m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g, SBV h, SBV i, SBV j) -> p) where
  proofArgReduce fn = mkArg >>= \a -> proofArgReduce $ \b c d e f g h i j -> fn (a, b, c, d, e, f, g, h, i, j)

-- 11 Tuple
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, SymVal h, SymVal i, SymVal j, SymVal k, SatisfiableM m p) => SatisfiableM m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g, SBV h, SBV i, SBV j, SBV k) -> p) where
  satArgReduce fn = mkArg >>= \a -> satArgReduce $ \b c d e f g h i j k -> fn (a, b, c, d, e, f, g, h, i, j, k)

instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, SymVal h, SymVal i, SymVal j, SymVal k, ProvableM m p) => ProvableM m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g, SBV h, SBV i, SBV j, SBV k) -> p) where
  proofArgReduce fn = mkArg >>= \a -> proofArgReduce $ \b c d e f g h i j k -> fn (a, b, c, d, e, f, g, h, i, j, k)

-- 12 Tuple
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, SymVal h, SymVal i, SymVal j, SymVal k, SymVal l, SatisfiableM m p) => SatisfiableM m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g, SBV h, SBV i, SBV j, SBV k, SBV l) -> p) where
  satArgReduce fn = mkArg >>= \a -> satArgReduce $ \b c d e f g h i j k l -> fn (a, b, c, d, e, f, g, h, i, j, k, l)

instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, SymVal h, SymVal i, SymVal j, SymVal k, SymVal l, ProvableM m p) => ProvableM m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g, SBV h, SBV i, SBV j, SBV k, SBV l) -> p) where
  proofArgReduce fn = mkArg >>= \a -> proofArgReduce $ \b c d e f g h i j k l -> fn (a, b, c, d, e, f, g, h, i, j, k, l)

-- | Generalization of 'Data.SBV.runSMT'
runSMT :: MonadIO m => SymbolicT m a -> m a
runSMT = runSMTWith defaultSMTCfg

-- | Generalization of 'Data.SBV.runSMTWith'
runSMTWith :: MonadIO m => SMTConfig -> SymbolicT m a -> m a
runSMTWith cfg a = fst <$> runSymbolic cfg (SMTMode QueryExternal ISetup True cfg) a

-- | Runs with a query.
runWithQuery :: ExtractIO m => (a -> SymbolicT m SBool) -> Bool -> QueryT m b -> SMTConfig -> a -> m b
runWithQuery reducer isSAT q cfg a = fst <$> runSymbolic cfg (SMTMode QueryInternal ISetup isSAT cfg) comp
  where comp =  do _ <- reducer a >>= output
                   Control.executeQuery QueryInternal q

-- | Check if a safe-call was safe or not, turning a t'SafeResult' to a Bool.
isSafe :: SafeResult -> Bool
isSafe (SafeResult (_, _, result)) = case result of
                                       Unsatisfiable{} -> True
                                       Satisfiable{}   -> False
                                       DeltaSat{}      -> False   -- conservative
                                       SatExtField{}   -> False   -- conservative
                                       Unknown{}       -> False   -- conservative
                                       ProofError{}    -> False   -- conservative

-- | Perform an action asynchronously, returning results together with diff-time.
runInThread :: NFData b => UTCTime -> (SMTConfig -> IO b) -> SMTConfig -> IO (Async (Solver, NominalDiffTime, b))
runInThread beginTime action config = async $ do
                result  <- action config
                endTime <- rnf result `seq` getCurrentTime
                pure (name (solver config), endTime `diffUTCTime` beginTime, result)

-- | Perform action for all given configs, return the first one that wins. Note that we do
-- not wait for the other asyncs to terminate; hopefully they'll do so quickly.
sbvWithAny :: NFData b => [SMTConfig] -> (SMTConfig -> a -> IO b) -> a -> IO (Solver, NominalDiffTime, b)
sbvWithAny []      _    _ = error "SBV.withAny: No solvers given!"
sbvWithAny solvers what a = do beginTime <- getCurrentTime
                               snd <$> (mapM (runInThread beginTime (`what` a)) solvers >>= waitAnyFastCancel)
   where -- Async's `waitAnyCancel` nicely blocks; so we use this variant to ignore the
         -- wait part for killed threads.
         waitAnyFastCancel asyncs = waitAny asyncs `finally` mapM_ cancelFast asyncs
         cancelFast other = throwTo (asyncThreadId other) ExitSuccess


sbvConcurrentWithAny :: NFData c => SMTConfig -> (SMTConfig -> a -> QueryT m b -> IO c) -> [QueryT m b] -> a -> IO (Solver, NominalDiffTime, c)
sbvConcurrentWithAny solver what queries a = snd <$> (mapM runQueryInThread queries >>= waitAnyFastCancel)
  where  -- Async's `waitAnyCancel` nicely blocks; so we use this variant to ignore the
         -- wait part for killed threads.
         waitAnyFastCancel asyncs = waitAny asyncs `finally` mapM_ cancelFast asyncs
         cancelFast other = throwTo (asyncThreadId other) ExitSuccess
         runQueryInThread q = do beginTime <- getCurrentTime
                                 runInThread beginTime (\cfg -> what cfg a q) solver


sbvConcurrentWithAll :: NFData c => SMTConfig -> (SMTConfig -> a -> QueryT m b -> IO c) -> [QueryT m b] -> a -> IO [(Solver, NominalDiffTime, c)]
sbvConcurrentWithAll solver what queries a = mapConcurrently runQueryInThread queries  >>= unsafeInterleaveIO . go
  where  runQueryInThread q = do beginTime <- getCurrentTime
                                 runInThread beginTime (\cfg -> what cfg a q) solver

         go []  = pure []
         go as  = do (d, r) <- waitAny as
                     -- The following filter works because the Eq instance on Async
                     -- checks the thread-id; so we know that we're removing the
                     -- correct solver from the list. This also allows for
                     -- running the same-solver (with different options), since
                     -- they will get different thread-ids.
                     rs <- unsafeInterleaveIO $ go (filter (/= d) as)
                     pure (r : rs)

-- | Perform action for all given configs, return all the results.
sbvWithAll :: NFData b => [SMTConfig] -> (SMTConfig -> a -> IO b) -> a -> IO [(Solver, NominalDiffTime, b)]
sbvWithAll solvers what a = do beginTime <- getCurrentTime
                               mapM (runInThread beginTime (`what` a)) solvers >>= (unsafeInterleaveIO . go)
   where go []  = pure []
         go as  = do (d, r) <- waitAny as
                     -- The following filter works because the Eq instance on Async
                     -- checks the thread-id; so we know that we're removing the
                     -- correct solver from the list. This also allows for
                     -- running the same-solver (with different options), since
                     -- they will get different thread-ids.
                     rs <- unsafeInterleaveIO $ go (filter (/= d) as)
                     pure (r : rs)

-- | Symbolically executable program fragments. This class is mainly used for 'safe' calls, and is sufficiently populated internally to cover most use
-- cases. Users can extend it as they wish to allow 'safe' checks for SBV programs that return/take types that are user-defined.
class ExtractIO m => SExecutable m a where
   -- | Generalization of 'Data.SBV.sName'
   sName :: a -> SymbolicT m ()

   -- | Generalization of 'Data.SBV.safe'
   safe :: a -> m [SafeResult]
   safe = safeWith defaultSMTCfg

   -- | Generalization of 'Data.SBV.safeWith'
   safeWith :: SMTConfig -> a -> m [SafeResult]
   safeWith cfg a = do cwd <- (++ "/") <$> liftIO getCurrentDirectory
                       let mkRelative path
                              | cwd `isPrefixOf` path = drop (length cwd) path
                              | True                  = path
                       fst <$> runSymbolic cfg (SMTMode QueryInternal ISafe True cfg) (sName a >> check mkRelative)
     where check :: (FilePath -> FilePath) -> SymbolicT m [SafeResult]
           check mkRelative = Control.executeQuery QueryInternal $ Control.getSBVAssertions >>= mapM (verify mkRelative)

           -- check that the cond is unsatisfiable. If satisfiable, that would
           -- indicate the assignment under which the 'Data.SBV.sAssert' would fail
           verify :: (FilePath -> FilePath) -> (String, Maybe CallStack, SV) -> QueryT m SafeResult
           verify mkRelative (msg, cs, cond) = do
                   let locInfo ps = let loc (f, sl) = concat [mkRelative (srcLocFile sl), ":", show (srcLocStartLine sl), ":", show (srcLocStartCol sl), ":", f]
                                    in intercalate ",\n " (map loc ps)
                       location   = locInfo . getCallStack <$> cs

                   result <- do Control.push 1
                                Control.send True $ "(assert " <> showText cond <> ")"
                                r <- Control.getSMTResult
                                Control.pop 1
                                pure r

                   pure $ SafeResult (location, msg, result)

instance (ExtractIO m, NFData a) => SExecutable m (SymbolicT m a) where
   sName a = a >>= \r -> rnf r `seq` pure ()

instance ExtractIO m => SExecutable m (SBV a) where
   sName v = sName (output v :: SymbolicT m (SBV a))

-- Unit output
instance ExtractIO m => SExecutable m () where
   sName () = sName (output () :: SymbolicT m ())

-- List output
instance ExtractIO m => SExecutable m [SBV a] where
   sName vs = sName (output vs :: SymbolicT m [SBV a])

-- 2 Tuple output
instance (ExtractIO m, NFData a, SymVal a, NFData b, SymVal b) => SExecutable m (SBV a, SBV b) where
  sName (a, b) = sName (output a >> output b :: SymbolicT m (SBV b))

-- 3 Tuple output
instance (ExtractIO m, NFData a, SymVal a, NFData b, SymVal b, NFData c, SymVal c) => SExecutable m (SBV a, SBV b, SBV c) where
  sName (a, b, c) = sName (output a >> output b >> output c :: SymbolicT m (SBV c))

-- 4 Tuple output
instance (ExtractIO m, NFData a, SymVal a, NFData b, SymVal b, NFData c, SymVal c, NFData d, SymVal d) => SExecutable m (SBV a, SBV b, SBV c, SBV d) where
  sName (a, b, c, d) = sName (output a >> output b >> output c >> output c >> output d :: SymbolicT m (SBV d))

-- 5 Tuple output
instance (ExtractIO m, NFData a, SymVal a, NFData b, SymVal b, NFData c, SymVal c, NFData d, SymVal d, NFData e, SymVal e) => SExecutable m (SBV a, SBV b, SBV c, SBV d, SBV e) where
  sName (a, b, c, d, e) = sName (output a >> output b >> output c >> output d >> output e :: SymbolicT m (SBV e))

-- 6 Tuple output
instance (ExtractIO m, NFData a, SymVal a, NFData b, SymVal b, NFData c, SymVal c, NFData d, SymVal d, NFData e, SymVal e, NFData f, SymVal f) => SExecutable m (SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) where
  sName (a, b, c, d, e, f) = sName (output a >> output b >> output c >> output d >> output e >> output f :: SymbolicT m (SBV f))

-- 7 Tuple output
instance (ExtractIO m, NFData a, SymVal a, NFData b, SymVal b, NFData c, SymVal c, NFData d, SymVal d, NFData e, SymVal e, NFData f, SymVal f, NFData g, SymVal g) => SExecutable m (SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) where
  sName (a, b, c, d, e, f, g) = sName (output a >> output b >> output c >> output d >> output e >> output f >> output g :: SymbolicT m (SBV g))

-- Functions
instance (SymVal a, SExecutable m p) => SExecutable m (SBV a -> p) where
   sName k = mkArg >>= \a -> sName $ k a

-- 2 Tuple input
instance (SymVal a, SymVal b, SExecutable m p) => SExecutable m ((SBV a, SBV b) -> p) where
  sName k = mkArg >>= \a -> sName $ \b -> k (a, b)

-- 3 Tuple input
instance (SymVal a, SymVal b, SymVal c, SExecutable m p) => SExecutable m ((SBV a, SBV b, SBV c) -> p) where
  sName k = mkArg >>= \a -> sName $ \b c -> k (a, b, c)

-- 4 Tuple input
instance (SymVal a, SymVal b, SymVal c, SymVal d, SExecutable m p) => SExecutable m ((SBV a, SBV b, SBV c, SBV d) -> p) where
  sName k = mkArg >>= \a -> sName $ \b c d -> k (a, b, c, d)

-- 5 Tuple input
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SExecutable m p) => SExecutable m ((SBV a, SBV b, SBV c, SBV d, SBV e) -> p) where
  sName k = mkArg >>= \a -> sName $ \b c d e -> k (a, b, c, d, e)

-- 6 Tuple input
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SExecutable m p) => SExecutable m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> p) where
  sName k = mkArg >>= \a -> sName $ \b c d e f -> k (a, b, c, d, e, f)

-- 7 Tuple input
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, SExecutable m p) => SExecutable m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> p) where
  sName k = mkArg >>= \a -> sName $ \b c d e f g -> k (a, b, c, d, e, f, g)

{- HLint ignore module "Reduce duplication" -}
