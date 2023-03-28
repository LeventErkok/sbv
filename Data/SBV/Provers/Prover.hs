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

{-# LANGUAGE CPP                   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Provers.Prover (
         SMTSolver(..), SMTConfig(..), Predicate
       , MProvable(..), Provable, MSatisfiable(..), Satisfiable
       , generateSMTBenchmarkSat, generateSMTBenchmarkProof, Goal
       , ThmResult(..), SatResult(..), AllSatResult(..), SafeResult(..), OptimizeResult(..), SMTResult(..)
       , SExecutable(..), isSafe
       , runSMT, runSMTWith
       , SatModel(..), Modelable(..), displayModels, extractModels
       , getModelDictionaries, getModelValues, getModelUninterpretedValues
       , abc, boolector, bitwuzla, cvc4, cvc5, dReal, mathSAT, yices, z3, defaultSMTCfg, defaultDeltaSMTCfg
       , SatArgReduce, ProofArgReduce
       ) where


import Control.Monad          (when, unless)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.DeepSeq        (rnf, NFData(..))

import Control.Concurrent.Async (async, waitAny, asyncThreadId, Async, mapConcurrently)
import Control.Exception (finally, throwTo)
import System.Exit (ExitCode(ExitSuccess))

import System.IO.Unsafe (unsafeInterleaveIO)             -- only used safely!

import System.Directory  (getCurrentDirectory)
import Data.Time (getZonedTime, NominalDiffTime, UTCTime, getCurrentTime, diffUTCTime)
import Data.List (intercalate, isPrefixOf)

import Data.Maybe (mapMaybe, listToMaybe)

import qualified Data.Foldable   as S (toList)
import qualified Data.Text       as T

import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic
import Data.SBV.SMT.SMT
import Data.SBV.SMT.Utils (debug, alignPlain)
import Data.SBV.Utils.ExtractIO
import Data.SBV.Utils.TDiff

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

import GHC.TypeLits

mkConfig :: SMTSolver -> SMTLibVersion -> [Control.SMTOption] -> SMTConfig
mkConfig s smtVersion startOpts = SMTConfig { verbose                     = False
                                            , timing                      = NoTiming
                                            , printBase                   = 10
                                            , printRealPrec               = 16
                                            , crackNum                    = False
                                            , transcript                  = Nothing
                                            , solver                      = s
                                            , smtLibVersion               = smtVersion
                                            , dsatPrecision               = Nothing
                                            , extraArgs                   = []
                                            , satCmd                      = "(check-sat)"
                                            , satTrackUFs                 = True                   -- i.e., yes, do extract UI function values
                                            , allSatMaxModelCount         = Nothing                -- i.e., return all satisfying models
                                            , allSatPrintAlong            = False                  -- i.e., do not print models as they are found
                                            , isNonModelVar               = const False            -- i.e., everything is a model-variable by default
                                            , validateModel               = False
                                            , optimizeValidateConstraints = False
                                            , roundingMode                = RoundNearestTiesToEven
                                            , solverSetOptions            = startOpts
                                            , ignoreExitCode              = False
                                            , redirectVerbose             = Nothing
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

-- | A goal is a symbolic program that returns no values. The idea is that the constraints/min-max
-- goals will serve as appropriate directives for sat/prove calls.
type Goal = Symbolic ()

-- | `Provable` is specialization of `MProvable` to the `IO` monad. Unless you are using
-- transformers explicitly, this is the type you should prefer.
type Provable = MProvable IO

-- | `Satisfiable` is specialization of `MSatisfiable` to the `IO` monad. Unless you are using
-- transformers explicitly, this is the type you should prefer.
type Satisfiable = MSatisfiable IO

-- | A class for capturing satisfiable arguments
class ExtractIO m => SatArgReduce m a where
   -- | Reduce an arg, for sat purposes. Typically not needed by end-users, unless you are
   -- writing a library on top of SBV that can manipulate properties.
  satArgReduce :: a -> SymbolicT m SBool

-- | A class for capturing provable arguments
class ExtractIO m => ProofArgReduce m a where
   -- | Reduce an arg, for proof purposes. Typically not needed by end-users, unless you are
   -- writing a library on top of SBV that can manipulate properties.
  proofArgReduce :: a -> SymbolicT m SBool

-- | A type @a@ is satisfiable if it has constraints, potentially returning a boolean. This class
-- captures essentially sat and optimize calls.
class ExtractIO m => MSatisfiable m a where
  -- | Generalization of 'Data.SBV.sat'
  sat :: a -> m SatResult

  default sat :: SatArgReduce m a => a -> m SatResult
  sat = satWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.satWith'
  satWith :: SMTConfig -> a -> m SatResult

  default satWith :: SatArgReduce m a => SMTConfig -> a -> m SatResult
  satWith cfg a = do r <- runWithQuery satArgReduce True (checkNoOptimizations >> Control.getSMTResult) cfg a
                     SatResult <$> if validationRequested cfg
                                   then validate satArgReduce True cfg a r
                                   else return r

  -- | Generalization of 'Data.SBV.sat'
  dsat :: a -> m SatResult
  dsat = dsatWith defaultDeltaSMTCfg

  -- | Generalization of 'Data.SBV.satWith'
  dsatWith :: SMTConfig -> a -> m SatResult

  default dsatWith :: SatArgReduce m a => SMTConfig -> a -> m SatResult
  dsatWith cfg a = do r <- runWithQuery satArgReduce True (checkNoOptimizations >> Control.getSMTResult) cfg a
                      SatResult <$> if validationRequested cfg
                                    then validate satArgReduce True cfg a r
                                    else return r

  -- | Generalization of 'Data.SBV.allSat'
  allSat :: a -> m AllSatResult
  allSat = allSatWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.allSatWith'
  allSatWith :: SMTConfig -> a -> m AllSatResult

  default allSatWith :: SatArgReduce m a => SMTConfig -> a -> m AllSatResult
  allSatWith cfg a = do asr <- runWithQuery satArgReduce True (checkNoOptimizations >> Control.getAllSatResult) cfg a
                        if validationRequested cfg
                           then do rs' <- mapM (validate satArgReduce True cfg a) (allSatResults asr)
                                   return asr{allSatResults = rs'}
                           else return asr

  -- | Generalization of 'Data.SBV.satIsVacuous'
  satIsVacuous :: a -> m Bool

  default satIsVacuous :: SatArgReduce m a => a -> m Bool
  satIsVacuous = isVacuousGen satArgReduce

  -- | Generalization of 'Data.SBV.satIsVacuousWith'
  satIsVacuousWith :: SMTConfig -> a -> m Bool

  default satIsVacuousWith :: SatArgReduce m a => SMTConfig -> a -> m Bool
  satIsVacuousWith = isVacuousWithGen satArgReduce

  -- | Generalization of 'Data.SBV.isSatisfiable'
  isSatisfiable :: a -> m Bool
  isSatisfiable = isSatisfiableWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.isSatisfiableWith'
  isSatisfiableWith :: SMTConfig -> a -> m Bool
  isSatisfiableWith cfg p = do r <- satWith cfg p
                               case r of
                                 SatResult Satisfiable{}   -> return True
                                 SatResult Unsatisfiable{} -> return False
                                 _                         -> error $ "SBV.isSatisfiable: Received: " ++ show r

  -- | Find a satisfying assignment to a property with multiple solvers, running them in separate threads. The
  -- results will be returned in the order produced.
  satWithAll :: [SMTConfig] -> a -> m [(Solver, NominalDiffTime, SatResult)]

  default satWithAll :: (m ~ IO) => [SMTConfig] -> a -> m [(Solver, NominalDiffTime, SatResult)]
  satWithAll = (`sbvWithAll` satWith)

  -- | Find a satisfying assignment to a property with multiple solvers, running them in separate threads. Only
  -- the result of the first one to finish will be returned, remaining threads will be killed.
  -- Note that we send an exception to the losing processes, but we do *not* actually wait for them
  -- to finish. In rare cases this can lead to zombie processes. In previous experiments, we found
  -- that some processes take their time to terminate. So, this solution favors quick turnaround.
  satWithAny :: [SMTConfig] -> a -> m (Solver, NominalDiffTime, SatResult)

  default satWithAny :: (m ~ IO) => [SMTConfig] -> a -> m (Solver, NominalDiffTime, SatResult)
  satWithAny = (`sbvWithAny` satWith)

  -- | Find a satisfying assignment to a property using a single solver, but
  -- providing several query problems of interest, with each query running in a
  -- separate thread and return the first one that returns. This can be useful to
  -- use symbolic mode to drive to a location in the search space of the solver
  -- and then refine the problem in query mode. If the computation is very hard to
  -- solve for the solver than running in concurrent mode may provide a large
  -- performance benefit.
  satConcurrentWithAny :: SMTConfig -> [QueryT m b] -> a -> m (Solver, NominalDiffTime, SatResult)

  default satConcurrentWithAny :: (m ~ IO, SatArgReduce m a) => SMTConfig -> [QueryT m b] -> a -> m (Solver, NominalDiffTime, SatResult)
  satConcurrentWithAny solver qs a = do (slvr,time,result) <- sbvConcurrentWithAny solver go qs a
                                        return (slvr, time, SatResult result)
    where go cfg a' q = runWithQuery satArgReduce True (do _ <- q; checkNoOptimizations >> Control.getSMTResult) cfg a'

  -- | Find a satisfying assignment to a property using a single solver, but run
  -- each query problem in a separate isolated thread and wait for each thread to
  -- finish. See 'satConcurrentWithAny' for more details.
  satConcurrentWithAll :: SMTConfig -> [QueryT m b] -> a -> m [(Solver, NominalDiffTime, SatResult)]

  default satConcurrentWithAll :: (m ~ IO, SatArgReduce m a) => SMTConfig -> [QueryT m b] -> a -> m [(Solver, NominalDiffTime, SatResult)]
  satConcurrentWithAll solver qs a = do results <- sbvConcurrentWithAll solver go qs a
                                        return $ (\(a',b,c) -> (a',b,SatResult c)) <$> results
    where go cfg a' q = runWithQuery satArgReduce True (do _ <- q; checkNoOptimizations >> Control.getSMTResult) cfg a'

  -- | Generalization of 'Data.SBV.optimize'
  optimize :: OptimizeStyle -> a -> m OptimizeResult
  optimize = optimizeWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.optimizeWith'
  optimizeWith :: SMTConfig -> OptimizeStyle -> a -> m OptimizeResult

  default optimizeWith :: SatArgReduce m a => SMTConfig -> OptimizeStyle -> a -> m OptimizeResult
  optimizeWith config style optGoal = do
                   res <- runWithQuery satArgReduce True opt config optGoal
                   if not (optimizeValidateConstraints config)
                      then return res
                      else let v :: SMTResult -> m SMTResult
                               v = validate satArgReduce True config optGoal
                           in case res of
                                LexicographicResult m -> LexicographicResult <$> v m
                                IndependentResult xs  -> let w []            sofar = return (reverse sofar)
                                                             w ((n, m):rest) sofar = v m >>= \m' -> w rest ((n, m') : sofar)
                                                         in IndependentResult <$> w xs []
                                ParetoResult (b, rs)  -> ParetoResult . (b, ) <$> mapM v rs

    where opt = do objectives <- Control.getObjectives

                   when (null objectives) $
                          error $ unlines [ ""
                                          , "*** Data.SBV: Unsupported call to optimize when no objectives are present."
                                          , "*** Use \"sat\" for plain satisfaction"
                                          ]

                   unless (supportsOptimization (capabilities (solver config))) $
                          error $ unlines [ ""
                                          , "*** Data.SBV: The backend solver " ++ show (name (solver config)) ++ "does not support optimization goals."
                                          , "*** Please use a solver that has support, such as z3"
                                          ]

                   when (validateModel config && not (optimizeValidateConstraints config)) $
                          error $ unlines [ ""
                                          , "*** Data.SBV: Model validation is not supported in optimization calls."
                                          , "***"
                                          , "*** Instead, use `cfg{optimizeValidateConstraints = True}`"
                                          , "***"
                                          , "*** which checks that the results satisfy the constraints but does"
                                          , "*** NOT ensure that they are optimal."
                                          ]


                   let optimizerDirectives = concatMap minmax objectives ++ priority style
                         where mkEq (x, y) = "(assert (= " ++ show x ++ " " ++ show y ++ "))"

                               minmax (Minimize          _  xy@(_, v))     = [mkEq xy, "(minimize "    ++ show v                 ++ ")"]
                               minmax (Maximize          _  xy@(_, v))     = [mkEq xy, "(maximize "    ++ show v                 ++ ")"]
                               minmax (AssertWithPenalty nm xy@(_, v) mbp) = [mkEq xy, "(assert-soft " ++ show v ++ penalize mbp ++ ")"]
                                 where penalize DefaultPenalty    = ""
                                       penalize (Penalty w mbGrp)
                                          | w <= 0         = error $ unlines [ "SBV.AssertWithPenalty: Goal " ++ show nm ++ " is assigned a non-positive penalty: " ++ shw
                                                                             , "All soft goals must have > 0 penalties associated."
                                                                             ]
                                          | True           = " :weight " ++ shw ++ maybe "" group mbGrp
                                          where shw = show (fromRational w :: Double)

                                       group g = " :id " ++ g

                               priority Lexicographic = [] -- default, no option needed
                               priority Independent   = ["(set-option :opt.priority box)"]
                               priority (Pareto _)    = ["(set-option :opt.priority pareto)"]

                   mapM_ (Control.send True) optimizerDirectives

                   case style of
                     Lexicographic -> LexicographicResult <$> Control.getLexicographicOptResults
                     Independent   -> IndependentResult   <$> Control.getIndependentOptResults (map objectiveName objectives)
                     Pareto mbN    -> ParetoResult        <$> Control.getParetoOptResults mbN


-- | A type @a@ is provable if we can turn it into a predicate, i.e., it has to return a boolean.
-- This class captures essentially prove calls.
class ExtractIO m => MProvable m a where
  -- | Generalization of 'Data.SBV.prove'
  prove :: a -> m ThmResult

  default prove :: ProofArgReduce m a => a -> m ThmResult
  prove = proveWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.proveWith'
  proveWith :: SMTConfig -> a -> m ThmResult

  default proveWith :: ProofArgReduce m a => SMTConfig -> a -> m ThmResult
  proveWith cfg a = do r <- runWithQuery proofArgReduce False (checkNoOptimizations >> Control.getSMTResult) cfg a
                       ThmResult <$> if validationRequested cfg
                                     then validate proofArgReduce False cfg a r
                                     else return r

  -- | Generalization of 'Data.SBV.dprove'
  dprove :: a -> m ThmResult
  dprove = dproveWith defaultDeltaSMTCfg

  -- | Generalization of 'Data.SBV.dproveWith'
  dproveWith :: SMTConfig -> a -> m ThmResult

  default dproveWith :: ProofArgReduce m a => SMTConfig -> a -> m ThmResult
  dproveWith cfg a = do r <- runWithQuery proofArgReduce False (checkNoOptimizations >> Control.getSMTResult) cfg a
                        ThmResult <$> if validationRequested cfg
                                      then validate proofArgReduce False cfg a r
                                      else return r

  -- | Generalization of 'Data.SBV.proofIsVacuous'
  proofIsVacuous :: a -> m Bool

  default proofIsVacuous :: ProofArgReduce m a => a -> m Bool
  proofIsVacuous = isVacuousGen proofArgReduce

  -- | Generalization of 'Data.SBV.proofIsVacuousWith'
  proofIsVacuousWith :: SMTConfig -> a -> m Bool

  default proofIsVacuousWith :: ProofArgReduce m a => SMTConfig -> a -> m Bool
  proofIsVacuousWith = isVacuousWithGen proofArgReduce

  -- | Generalization of 'Data.SBV.isTheorem'
  isTheorem :: a -> m Bool
  isTheorem = isTheoremWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.isTheoremWith'
  isTheoremWith :: SMTConfig -> a -> m Bool
  isTheoremWith cfg p = do r <- proveWith cfg p
                           let bad = error $ "SBV.isTheorem: Received:\n" ++ show r
                           case r of
                             ThmResult Unsatisfiable{} -> return True
                             ThmResult Satisfiable{}   -> return False
                             ThmResult DeltaSat{}      -> return False
                             ThmResult SatExtField{}   -> return False
                             ThmResult Unknown{}       -> bad
                             ThmResult ProofError{}    -> bad

  -- | Prove a property with multiple solvers, running them in separate threads. The
  -- results will be returned in the order produced.
  proveWithAll :: [SMTConfig] -> a -> m [(Solver, NominalDiffTime, ThmResult)]

  default proveWithAll :: (m ~ IO) => [SMTConfig] -> a -> m [(Solver, NominalDiffTime, ThmResult)]
  proveWithAll  = (`sbvWithAll` proveWith)

  -- | Prove a property with multiple solvers, running them in separate threads. Only
  -- the result of the first one to finish will be returned, remaining threads will be killed.
  -- Note that we send an exception to the losing processes, but we do *not* actually wait for them
  -- to finish. In rare cases this can lead to zombie processes. In previous experiments, we found
  -- that some processes take their time to terminate. So, this solution favors quick turnaround.
  proveWithAny :: [SMTConfig] -> a -> m (Solver, NominalDiffTime, ThmResult)

  default proveWithAny :: (m ~ IO) => [SMTConfig] -> a -> m (Solver, NominalDiffTime, ThmResult)
  proveWithAny  = (`sbvWithAny` proveWith)

  -- | Prove a property by running many queries each isolated to their own thread
  -- concurrently and return the first that finishes, killing the others
  proveConcurrentWithAny :: SMTConfig -> [QueryT m b] -> a -> m (Solver, NominalDiffTime, ThmResult)

  default proveConcurrentWithAny :: (m ~ IO) => ProofArgReduce m a => SMTConfig -> [QueryT m b] -> a -> m (Solver, NominalDiffTime, ThmResult)
  proveConcurrentWithAny solver qs a = do (slvr,time,result) <- sbvConcurrentWithAny solver go qs a
                                          return (slvr, time, ThmResult result)
    where go cfg a' q = runWithQuery proofArgReduce False (do _ <- q;  checkNoOptimizations >> Control.getSMTResult) cfg a'

  -- | Prove a property by running many queries each isolated to their own thread
  -- concurrently and wait for each to finish returning all results
  proveConcurrentWithAll :: SMTConfig -> [QueryT m b] -> a -> m [(Solver, NominalDiffTime, ThmResult)]

  default proveConcurrentWithAll :: (m ~ IO, ProofArgReduce m a) => SMTConfig -> [QueryT m b] -> a -> m [(Solver, NominalDiffTime, ThmResult)]
  proveConcurrentWithAll solver qs a = do results <- sbvConcurrentWithAll solver go qs a
                                          return $ (\(a',b,c) -> (a',b,ThmResult c)) <$> results
    where go cfg a' q = runWithQuery proofArgReduce False (do _ <- q; checkNoOptimizations >> Control.getSMTResult) cfg a'


-- | Validate a model obtained from the solver
validate :: MonadIO m => (a -> SymbolicT m SBool) -> Bool -> SMTConfig -> a -> SMTResult -> m SMTResult
validate reducer isSAT cfg p res =
     case res of
       Unsatisfiable{} -> return res
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

       Unknown{}       -> return res
       ProofError{}    -> return res

  where cant msg = return $ ProofError cfg (msg ++ [ ""
                                                   , "Unable to validate the produced model."
                                                   ]) (Just res)

        check env = do let envShown = showModelDictionary True True cfg modelBinds
                              where modelBinds = [(T.unpack n, RegularCV v) | (NamedSymVar _ n, v) <- env]

                           notify s
                             | not (verbose cfg) = return ()
                             | True              = debug cfg ["[VALIDATE] " `alignPlain` s]

                       notify $ "Validating the model. " ++ if null env then "There are no assignments." else "Assignment:"
                       mapM_ notify ["    " ++ l | l <- lines envShown]

                       result <- snd <$> runSymbolic cfg (Concrete (Just (isSAT, env))) (reducer p >>= output)

                       let explain  = [ ""
                                      , "Assignment:"  ++ if null env then " <none>" else ""
                                      ]
                                   ++ [ ""          | not (null env)]
                                   ++ [ "    " ++ l | l <- lines envShown]
                                   ++ [ "" ]

                           wrap tag extras = return $ ProofError cfg (tag : explain ++ extras) (Just res)

                           giveUp   s     = wrap ("Data.SBV: Cannot validate the model: " ++ s)
                                                 [ "SBV's model validator is incomplete, and cannot handle this particular case."
                                                 , "Please report this as a feature request or possibly a bug!"
                                                 ]

                           badModel s     = wrap ("Data.SBV: Model validation failure: " ++ s)
                                                 [ "Backend solver returned a model that does not satisfy the constraints."
                                                 , "This could indicate a bug in the backend solver, or SBV itself. Please report."
                                                 ]

                           notConcrete sv = wrap ("Data.SBV: Cannot validate the model, since " ++ show sv ++ " is not concretely computable.")
                                                 (  perhaps (why sv)
                                                 ++ [ "SBV's model validator is incomplete, and cannot handle this particular case."
                                                    , "Please report this as a feature request or possibly a bug!"
                                                    ]
                                                 )
                                where perhaps Nothing  = []
                                      perhaps (Just x) = [x, ""]

                                      -- This is incomplete, but should capture the most common cases
                                      why s = case s `lookup` S.toList (pgmAssignments (resAsgns result)) of
                                                Nothing            -> Nothing
                                                Just (SBVApp o as) -> case o of
                                                                        Uninterpreted v   -> Just $ "The value depends on the uninterpreted constant " ++ show v ++ "."
                                                                        QuantifiedBool _  -> Just "The value depends on a quantified variable."
                                                                        IEEEFP FP_FMA     -> Just "Floating point FMA operation is not supported concretely."
                                                                        IEEEFP _          -> Just "Not all floating point operations are supported concretely."
                                                                        OverflowOp _      -> Just "Overflow-checking is not done concretely."
                                                                        _                 -> listToMaybe $ mapMaybe why as

                           cstrs = S.toList $ resConstraints result

                           walkConstraints [] cont = do
                              unless (null cstrs) $ notify "Validated all constraints."
                              cont
                           walkConstraints ((isSoft, attrs, sv) : rest) cont
                              | kindOf sv /= KBool
                              = giveUp $ "Constraint tied to " ++ show sv ++ " is non-boolean."
                              | isSoft || sv == trueSV
                              = walkConstraints rest cont
                              | sv == falseSV
                              = case mbName of
                                  Just nm -> badModel $ "Named constraint " ++ show nm ++ " evaluated to False."
                                  Nothing -> badModel "A constraint was violated."
                              | True
                              = notConcrete sv
                              where mbName = listToMaybe [n | (":named", n) <- attrs]

                           -- SAT: All outputs must be true
                           satLoop []
                             = do notify "All outputs are satisfied. Validation complete."
                                  return res
                           satLoop (sv:svs)
                             | kindOf sv /= KBool
                             = giveUp $ "Output tied to " ++ show sv ++ " is non-boolean."
                             | sv == trueSV
                             = satLoop svs
                             | sv == falseSV
                             = badModel "Final output evaluated to False."
                             | True
                             = notConcrete sv

                           -- Proof: At least one output must be false
                           proveLoop [] somethingFailed
                             | somethingFailed = do notify "Counterexample is validated."
                                                    return res
                             | True            = do notify "Counterexample violates none of the outputs."
                                                    badModel "Counter-example violates no constraints."
                           proveLoop (sv:svs) somethingFailed
                             | kindOf sv /= KBool
                             = giveUp $ "Output tied to " ++ show sv ++ " is non-boolean."
                             | sv == trueSV
                             = proveLoop svs somethingFailed
                             | sv == falseSV
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

-- | Check vacuity helper
isVacuousGen :: ExtractIO m => (a -> SymbolicT m SBool) -> a -> m Bool
isVacuousGen reducer = isVacuousWithGen reducer defaultSMTCfg

-- | Check vacuity helper with config
isVacuousWithGen :: ExtractIO m => (a -> SymbolicT m SBool) -> SMTConfig -> a -> m Bool
isVacuousWithGen reducer cfg a = -- NB. Can't call runWithQuery since last constraint would become the implication!
       fst <$> runSymbolic cfg (SMTMode QueryInternal ISetup True cfg) (reducer a >> Control.executeQuery QueryInternal check)
     where
       check = do cs <- Control.checkSat
                  case cs of
                    Control.Unsat  -> return True
                    Control.Sat    -> return False
                    Control.DSat{} -> return False
                    Control.Unk    -> error "SBV: isVacuous: Solver returned unknown!"

-- | Create an SMT-Lib2 benchmark, for a SAT query.
generateSMTBenchmarkSat :: SatArgReduce m a => a -> m String
generateSMTBenchmarkSat = generateSMTBenchMarkGen True satArgReduce

-- | Create an SMT-Lib2 benchmark, for a Proof query.
generateSMTBenchmarkProof :: ProofArgReduce m a => a -> m String
generateSMTBenchmarkProof = generateSMTBenchMarkGen False proofArgReduce

-- | Generic benchmark creator
generateSMTBenchMarkGen :: MonadIO m => Bool -> (a -> SymbolicT m SBool) -> a -> m String
generateSMTBenchMarkGen isSat reduce a = do
      t <- liftIO getZonedTime

      let comments = ["Automatically created by SBV on " ++ show t]
          cfg      = defaultSMTCfg { smtLibVersion = SMTLib2 }

      (_, res) <- runSymbolic cfg (SMTMode QueryInternal ISetup isSat cfg) $ reduce a >>= output

      let SMTProblem{smtLibPgm} = Control.runProofOn (SMTMode QueryInternal IRun isSat cfg) QueryInternal comments res
          out                   = show (smtLibPgm cfg)

      return $ out ++ "\n(check-sat)\n"

checkNoOptimizations :: MonadIO m => QueryT m ()
checkNoOptimizations = do objectives <- Control.getObjectives

                          unless (null objectives) $
                                error $ unlines [ ""
                                                , "*** Data.SBV: Unsupported call sat/prove when optimization objectives are present."
                                                , "*** Use \"optimize\"/\"optimizeWith\" to calculate optimal satisfaction!"
                                                ]

instance SatArgReduce   IO a => MSatisfiable IO a
instance ProofArgReduce IO a => MProvable    IO a

instance ExtractIO m => SatArgReduce m (SymbolicT m ()) where satArgReduce a = satArgReduce ((a >> pure sTrue) :: SymbolicT m SBool)
-- instance ExtractIO m => ProofArgReduce m (SymbolicT m ())  -- NO INSTANCE ON PURPOSE; don't want to prove goals

instance ExtractIO m => SatArgReduce   m (SymbolicT m SBool) where satArgReduce   = id
instance ExtractIO m => ProofArgReduce m (SymbolicT m SBool) where proofArgReduce = id

instance ExtractIO m => SatArgReduce   m SBool where satArgReduce   = return
instance ExtractIO m => ProofArgReduce m SBool where proofArgReduce = return

instance (ExtractIO m, SymVal a, Constraint Symbolic r, SatArgReduce m r) => SatArgReduce m (Forall a -> r) where
  satArgReduce = satArgReduce . quantifiedBool

instance (ExtractIO m, SymVal a, Constraint Symbolic r, ProofArgReduce m r) => ProofArgReduce m (Forall a -> r) where
  proofArgReduce = proofArgReduce . quantifiedBool

instance (ExtractIO m, SymVal a, Constraint Symbolic r, SatArgReduce m r) => SatArgReduce m (Exists a -> r) where
  satArgReduce = satArgReduce . quantifiedBool

instance (KnownNat n, ExtractIO m, SymVal a, Constraint Symbolic r, ProofArgReduce m r) => ProofArgReduce m (ForallN n a -> r) where
  proofArgReduce = proofArgReduce . quantifiedBool

instance (KnownNat n, ExtractIO m, SymVal a, Constraint Symbolic r, SatArgReduce m r) => SatArgReduce m (ExistsN n a -> r) where
  satArgReduce = satArgReduce . quantifiedBool

instance (ExtractIO m, SymVal a, Constraint Symbolic r, ProofArgReduce m r) => ProofArgReduce m (Exists a -> r) where
  proofArgReduce = proofArgReduce . quantifiedBool

instance (KnownNat n, ExtractIO m, SymVal a, Constraint Symbolic r, SatArgReduce m r) => SatArgReduce m (ForallN n a -> r) where
  satArgReduce = satArgReduce . quantifiedBool

instance (KnownNat n, ExtractIO m, SymVal a, Constraint Symbolic r, ProofArgReduce m r) => ProofArgReduce m (ExistsN n a -> r) where
  proofArgReduce = proofArgReduce . quantifiedBool

{-
-- The following works, but it lets us write properties that
-- are not useful.. Such as: prove $ \x y -> (x::SInt8) == y
-- Running that will throw an exception since Haskell's equality
-- is not be supported by symbolic things. (Needs .==).
instance Provable Bool where
  argReduce  x  = argReduce  (if x then true else false :: SBool)
  argReduce s x  = argReduce s (if x then true else false :: SBool)
-}

-- | Create an argument
mkArg :: (SymVal a, MonadSymbolic m) => m (SBV a)
mkArg = mkSymVal (NonQueryVar Nothing) Nothing

-- Functions
instance (SymVal a, SatArgReduce m p) => SatArgReduce m (SBV a -> p) where
  satArgReduce k = mkArg >>= \a -> satArgReduce $ k a

instance (SymVal a, ProofArgReduce m p) => ProofArgReduce m (SBV a -> p) where
  proofArgReduce k = mkArg >>= \a -> proofArgReduce $ k a

-- Arrays
instance (HasKind a, HasKind b, SatArgReduce m p) => SatArgReduce m (SArray a b -> p) where
  satArgReduce k = newArray_ Nothing >>= \a -> satArgReduce $ k a

instance (HasKind a, HasKind b, ProofArgReduce m p) => ProofArgReduce m (SArray a b -> p) where
  proofArgReduce k = newArray_ Nothing >>= \a -> proofArgReduce $ k a

-- 2 Tuple
instance (SymVal a, SymVal b, SatArgReduce m p) => SatArgReduce m ((SBV a, SBV b) -> p) where
  satArgReduce k = mkArg >>= \a -> satArgReduce $ \b -> k (a, b)

instance (SymVal a, SymVal b, ProofArgReduce m p) => ProofArgReduce m ((SBV a, SBV b) -> p) where
  proofArgReduce k = mkArg >>= \a -> proofArgReduce $ \b -> k (a, b)

-- 3 Tuple
instance (SymVal a, SymVal b, SymVal c, SatArgReduce m p) => SatArgReduce m ((SBV a, SBV b, SBV c) -> p) where
  satArgReduce k = mkArg >>= \a -> satArgReduce $ \b c -> k (a, b, c)

instance (SymVal a, SymVal b, SymVal c, ProofArgReduce m p) => ProofArgReduce m ((SBV a, SBV b, SBV c) -> p) where
  proofArgReduce k = mkArg >>= \a -> proofArgReduce $ \b c -> k (a, b, c)

-- 4 Tuple
instance (SymVal a, SymVal b, SymVal c, SymVal d, SatArgReduce m p) => SatArgReduce m ((SBV a, SBV b, SBV c, SBV d) -> p) where
  satArgReduce k = mkArg  >>= \a -> satArgReduce $ \b c d -> k (a, b, c, d)

instance (SymVal a, SymVal b, SymVal c, SymVal d, ProofArgReduce m p) => ProofArgReduce m ((SBV a, SBV b, SBV c, SBV d) -> p) where
  proofArgReduce k = mkArg  >>= \a -> proofArgReduce $ \b c d -> k (a, b, c, d)

-- 5 Tuple
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SatArgReduce m p) => SatArgReduce m ((SBV a, SBV b, SBV c, SBV d, SBV e) -> p) where
  satArgReduce k = mkArg >>= \a -> satArgReduce $ \b c d e -> k (a, b, c, d, e)

instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, ProofArgReduce m p) => ProofArgReduce m ((SBV a, SBV b, SBV c, SBV d, SBV e) -> p) where
  proofArgReduce k = mkArg >>= \a -> proofArgReduce $ \b c d e -> k (a, b, c, d, e)

-- 6 Tuple
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SatArgReduce m p) => SatArgReduce m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> p) where
  satArgReduce k = mkArg >>= \a -> satArgReduce $ \b c d e f -> k (a, b, c, d, e, f)

instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, ProofArgReduce m p) => ProofArgReduce m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> p) where
  proofArgReduce k = mkArg >>= \a -> proofArgReduce $ \b c d e f -> k (a, b, c, d, e, f)

-- 7 Tuple
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, SatArgReduce m p) => SatArgReduce m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> p) where
  satArgReduce k = mkArg >>= \a -> satArgReduce $ \b c d e f g -> k (a, b, c, d, e, f, g)

instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, ProofArgReduce m p) => ProofArgReduce m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> p) where
  proofArgReduce k = mkArg >>= \a -> proofArgReduce $ \b c d e f g -> k (a, b, c, d, e, f, g)

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

-- | Check if a safe-call was safe or not, turning a 'SafeResult' to a Bool.
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
                return (name (solver config), endTime `diffUTCTime` beginTime, result)

-- | Perform action for all given configs, return the first one that wins. Note that we do
-- not wait for the other asyncs to terminate; hopefully they'll do so quickly.
sbvWithAny :: NFData b => [SMTConfig] -> (SMTConfig -> a -> IO b) -> a -> IO (Solver, NominalDiffTime, b)
sbvWithAny []      _    _ = error "SBV.withAny: No solvers given!"
sbvWithAny solvers what a = do beginTime <- getCurrentTime
                               snd `fmap` (mapM (runInThread beginTime (`what` a)) solvers >>= waitAnyFastCancel)
   where -- Async's `waitAnyCancel` nicely blocks; so we use this variant to ignore the
         -- wait part for killed threads.
         waitAnyFastCancel asyncs = waitAny asyncs `finally` mapM_ cancelFast asyncs
         cancelFast other = throwTo (asyncThreadId other) ExitSuccess


sbvConcurrentWithAny :: NFData c => SMTConfig -> (SMTConfig -> a -> QueryT m b -> IO c) -> [QueryT m b] -> a -> IO (Solver, NominalDiffTime, c)
sbvConcurrentWithAny solver what queries a = snd `fmap` (mapM runQueryInThread queries >>= waitAnyFastCancel)
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

         go []  = return []
         go as  = do (d, r) <- waitAny as
                     -- The following filter works because the Eq instance on Async
                     -- checks the thread-id; so we know that we're removing the
                     -- correct solver from the list. This also allows for
                     -- running the same-solver (with different options), since
                     -- they will get different thread-ids.
                     rs <- unsafeInterleaveIO $ go (filter (/= d) as)
                     return (r : rs)

-- | Perform action for all given configs, return all the results.
sbvWithAll :: NFData b => [SMTConfig] -> (SMTConfig -> a -> IO b) -> a -> IO [(Solver, NominalDiffTime, b)]
sbvWithAll solvers what a = do beginTime <- getCurrentTime
                               mapM (runInThread beginTime (`what` a)) solvers >>= (unsafeInterleaveIO . go)
   where go []  = return []
         go as  = do (d, r) <- waitAny as
                     -- The following filter works because the Eq instance on Async
                     -- checks the thread-id; so we know that we're removing the
                     -- correct solver from the list. This also allows for
                     -- running the same-solver (with different options), since
                     -- they will get different thread-ids.
                     rs <- unsafeInterleaveIO $ go (filter (/= d) as)
                     return (r : rs)

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
                       location   = (locInfo . getCallStack) `fmap` cs

                   result <- do Control.push 1
                                Control.send True $ "(assert " ++ show cond ++ ")"
                                r <- Control.getSMTResult
                                Control.pop 1
                                return r

                   return $ SafeResult (location, msg, result)

instance (ExtractIO m, NFData a) => SExecutable m (SymbolicT m a) where
   sName a = a >>= \r -> rnf r `seq` return ()

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

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
