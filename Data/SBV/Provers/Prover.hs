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
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Provers.Prover (
         SMTSolver(..), SMTConfig(..), Predicate
       , MProvable(..), Provable, proveWithAll, proveWithAny , satWithAll, satWithAny
       , satConcurrentWithAny, satConcurrentWithAll, proveConcurrentWithAny, proveConcurrentWithAll
       , generateSMTBenchmark
       , Goal
       , ThmResult(..), SatResult(..), AllSatResult(..), SafeResult(..), OptimizeResult(..), SMTResult(..)
       , SExecutable(..), isSafe
       , runSMT, runSMTWith
       , SatModel(..), Modelable(..), displayModels, extractModels
       , getModelDictionaries, getModelValues, getModelUninterpretedValues
       , abc, boolector, bitwuzla, cvc4, cvc5, dReal, mathSAT, yices, z3, defaultSMTCfg, defaultDeltaSMTCfg
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
import Data.IORef (readIORef)

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

-- | A type @a@ is provable if we can turn it into a predicate.
-- Note that a predicate can be made from a curried function of arbitrary arity, where
-- each element is either a symbolic type or up-to a 7-tuple of symbolic-types. So
-- predicates can be constructed from almost arbitrary Haskell functions that have arbitrary
-- shapes. (See the instance declarations below.)
class ExtractIO m => MProvable m a where
  -- | Turn a value into a predicate, by providing an parameter as argument.
  argReduce :: a -> SymbolicT m SBool

  -- | Generalization of 'Data.SBV.prove'
  prove :: a -> m ThmResult
  prove = proveWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.proveWith'
  proveWith :: SMTConfig -> a -> m ThmResult
  proveWith cfg a = do r <- runWithQuery False (checkNoOptimizations >> Control.getSMTResult) cfg a
                       ThmResult <$> if validationRequested cfg
                                     then validate False cfg a r
                                     else return r

  -- | Generalization of 'Data.SBV.dprove'
  dprove :: a -> m ThmResult
  dprove = dproveWith defaultDeltaSMTCfg

  -- | Generalization of 'Data.SBV.dproveWith'
  dproveWith :: SMTConfig -> a -> m ThmResult
  dproveWith cfg a = do r <- runWithQuery False (checkNoOptimizations >> Control.getSMTResult) cfg a
                        ThmResult <$> if validationRequested cfg
                                      then validate False cfg a r
                                      else return r

  -- | Generalization of 'Data.SBV.sat'
  sat :: a -> m SatResult
  sat = satWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.satWith'
  satWith :: SMTConfig -> a -> m SatResult
  satWith cfg a = do r <- runWithQuery True (checkNoOptimizations >> Control.getSMTResult) cfg a
                     SatResult <$> if validationRequested cfg
                                   then validate True cfg a r
                                   else return r

  -- | Generalization of 'Data.SBV.sat'
  dsat :: a -> m SatResult
  dsat = dsatWith defaultDeltaSMTCfg

  -- | Generalization of 'Data.SBV.satWith'
  dsatWith :: SMTConfig -> a -> m SatResult
  dsatWith cfg a = do r <- runWithQuery True (checkNoOptimizations >> Control.getSMTResult) cfg a
                      SatResult <$> if validationRequested cfg
                                    then validate True cfg a r
                                    else return r

  -- | Generalization of 'Data.SBV.allSat'
  allSat :: a -> m AllSatResult
  allSat = allSatWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.allSatWith'
  allSatWith :: SMTConfig -> a -> m AllSatResult
  allSatWith cfg a = do asr <- runWithQuery True (checkNoOptimizations >> Control.getAllSatResult) cfg a
                        if validationRequested cfg
                           then do rs' <- mapM (validate True cfg a) (allSatResults asr)
                                   return asr{allSatResults = rs'}
                           else return asr

  -- | Generalization of 'Data.SBV.optimize'
  optimize :: OptimizeStyle -> a -> m OptimizeResult
  optimize = optimizeWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.optimizeWith'
  optimizeWith :: SMTConfig -> OptimizeStyle -> a -> m OptimizeResult
  optimizeWith config style optGoal = do
                   res <- runWithQuery True opt config optGoal
                   if not (optimizeValidateConstraints config)
                      then return res
                      else let v :: SMTResult -> m SMTResult
                               v = validate True config optGoal
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

  -- | Generalization of 'Data.SBV.isVacuous'
  isVacuous :: a -> m Bool
  isVacuous = isVacuousWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.isVacuousWith'
  isVacuousWith :: SMTConfig -> a -> m Bool
  isVacuousWith cfg a = -- NB. Can't call runWithQuery since last constraint would become the implication!
       fst <$> runSymbolic cfg (SMTMode QueryInternal ISetup True cfg) (argReduce a >> Control.executeQuery QueryInternal check)
     where
       check :: QueryT m Bool
       check = do cs <- Control.checkSat
                  case cs of
                    Control.Unsat  -> return True
                    Control.Sat    -> return False
                    Control.DSat{} -> return False
                    Control.Unk    -> error "SBV: isVacuous: Solver returned unknown!"

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

  -- | Validate a model obtained from the solver
  validate :: Bool -> SMTConfig -> a -> SMTResult -> m SMTResult
  validate isSAT cfg p res = case res of
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

                         result <- snd <$> runSymbolic cfg (Concrete (Just (isSAT, env))) (argReduce p >>= output)

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

-- | `Provable` is specialization of `MProvable` to the `IO` monad. Unless you are using
-- transformers explicitly, this is the type you should prefer.
type Provable = MProvable IO

-- | Prove a property with multiple solvers, running them in separate threads. The
-- results will be returned in the order produced.
proveWithAll :: Provable a => [SMTConfig] -> a -> IO [(Solver, NominalDiffTime, ThmResult)]
proveWithAll  = (`sbvWithAll` proveWith)

-- | Prove a property with multiple solvers, running them in separate threads. Only
-- the result of the first one to finish will be returned, remaining threads will be killed.
-- Note that we send an exception to the losing processes, but we do *not* actually wait for them
-- to finish. In rare cases this can lead to zombie processes. In previous experiments, we found
-- that some processes take their time to terminate. So, this solution favors quick turnaround.
proveWithAny :: Provable a => [SMTConfig] -> a -> IO (Solver, NominalDiffTime, ThmResult)
proveWithAny  = (`sbvWithAny` proveWith)

-- | Find a satisfying assignment to a property with multiple solvers, running them in separate threads. The
-- results will be returned in the order produced.
satWithAll :: Provable a => [SMTConfig] -> a -> IO [(Solver, NominalDiffTime, SatResult)]
satWithAll = (`sbvWithAll` satWith)

-- | Find a satisfying assignment to a property with multiple solvers, running them in separate threads. Only
-- the result of the first one to finish will be returned, remaining threads will be killed.
-- Note that we send an exception to the losing processes, but we do *not* actually wait for them
-- to finish. In rare cases this can lead to zombie processes. In previous experiments, we found
-- that some processes take their time to terminate. So, this solution favors quick turnaround.
satWithAny :: Provable a => [SMTConfig] -> a -> IO (Solver, NominalDiffTime, SatResult)
satWithAny = (`sbvWithAny` satWith)

-- | Find a satisfying assignment to a property using a single solver, but
-- providing several query problems of interest, with each query running in a
-- separate thread and return the first one that returns. This can be useful to
-- use symbolic mode to drive to a location in the search space of the solver
-- and then refine the problem in query mode. If the computation is very hard to
-- solve for the solver than running in concurrent mode may provide a large
-- performance benefit.
satConcurrentWithAny :: Provable a => SMTConfig -> [Query b] -> a -> IO (Solver, NominalDiffTime, SatResult)
satConcurrentWithAny solver qs a = do (slvr,time,result) <- sbvConcurrentWithAny solver go qs a
                                      return (slvr, time, SatResult result)
  where go cfg a' q = runWithQuery True (do _ <- q; checkNoOptimizations >> Control.getSMTResult) cfg a'

-- | Prove a property by running many queries each isolated to their own thread
-- concurrently and return the first that finishes, killing the others
proveConcurrentWithAny :: Provable a => SMTConfig -> [Query b] -> a -> IO (Solver, NominalDiffTime, ThmResult)
proveConcurrentWithAny solver qs a = do (slvr,time,result) <- sbvConcurrentWithAny solver go qs a
                                        return (slvr, time, ThmResult result)
  where go cfg a' q = runWithQuery False (do _ <- q;  checkNoOptimizations >> Control.getSMTResult) cfg a'

-- | Find a satisfying assignment to a property using a single solver, but run
-- each query problem in a separate isolated thread and wait for each thread to
-- finish. See 'satConcurrentWithAny' for more details.
satConcurrentWithAll :: Provable a => SMTConfig -> [Query b] -> a -> IO [(Solver, NominalDiffTime, SatResult)]
satConcurrentWithAll solver qs a = do results <- sbvConcurrentWithAll solver go qs a
                                      return $ (\(a',b,c) -> (a',b,SatResult c)) <$> results
  where go cfg a' q = runWithQuery True (do _ <- q; checkNoOptimizations >> Control.getSMTResult) cfg a'

-- | Prove a property by running many queries each isolated to their own thread
-- concurrently and wait for each to finish returning all results
proveConcurrentWithAll :: Provable a => SMTConfig -> [Query b] -> a -> IO [(Solver, NominalDiffTime, ThmResult)]
proveConcurrentWithAll solver qs a = do results <- sbvConcurrentWithAll solver go qs a
                                        return $ (\(a',b,c) -> (a',b,ThmResult c)) <$> results
  where go cfg a' q = runWithQuery False (do _ <- q; checkNoOptimizations >> Control.getSMTResult) cfg a'

-- | Create an SMT-Lib2 benchmark. The 'Bool' argument controls whether this is a SAT instance, i.e.,
-- translate the query directly, or a PROVE instance, i.e., translate the negated query.
generateSMTBenchmark :: (MonadIO m, MProvable m a) => Bool -> a -> m String
generateSMTBenchmark isSat a = do
      t <- liftIO getZonedTime

      let comments = ["Automatically created by SBV on " ++ show t]
          cfg      = defaultSMTCfg { smtLibVersion = SMTLib2 }

      (_, res) <- runSymbolic cfg (SMTMode QueryInternal ISetup isSat cfg) $ argReduce a >>= output

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

-- If we get a program producing nothing (i.e., Symbolic ()), pretend it returns True if we're in a SAT-context,
-- and it returns False in a proof-context. This is useful since min/max calls and constraints will provide the
-- necessary constraints.
instance ExtractIO m => MProvable m (SymbolicT m ()) where
  argReduce a = finalizer >>= \b -> argReduce ((a >> pure b) :: SymbolicT m SBool)

-- If we're in a proof mode, return sFalse. If SAT, return sTrue.
finalizer :: MonadSymbolic m => m SBool
finalizer = do st <- symbolicEnv
               rm <- liftIO $ readIORef (runMode st)
               case rm of
                 SMTMode _ _ isSat _ -> pure $ if isSat then sTrue else sFalse
                 CodeGen{}           -> nope rm
                 LambdaGen{}         -> nope rm
                 Concrete{}          -> nope rm
  where nope rm = error $ unlines
                          [ ""
                          , "*** Data.SBV: Impossible happened. Unexpected call to finalizer in a non-proof context"
                          , "***"
                          , "***   Found mode: " ++ show rm
                          , "***"
                          , "*** Was expecting to be in a sat/prove call."
                          ]

instance ExtractIO m => MProvable m (SymbolicT m SBool) where
  argReduce = id

instance ExtractIO m => MProvable m SBool where
  argReduce = return

instance (ExtractIO m, SymVal a, Constraint Symbolic r) => MProvable m (Forall a -> r) where
  argReduce = argReduce . quantifiedBool

instance (ExtractIO m, SymVal a, Constraint Symbolic r) => MProvable m (Exists a -> r) where
  argReduce = argReduce . quantifiedBool

instance (KnownNat n, ExtractIO m, SymVal a, Constraint Symbolic r) => MProvable m (ForallN n a -> r) where
  argReduce = argReduce . quantifiedBool

instance (KnownNat n, ExtractIO m, SymVal a, Constraint Symbolic r) => MProvable m (ExistsN n a -> r) where
  argReduce = argReduce . quantifiedBool

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
instance (SymVal a, MProvable m p) => MProvable m (SBV a -> p) where
  argReduce k = mkArg >>= \a -> argReduce $ k a

-- Arrays
instance (HasKind a, HasKind b, MProvable m p) => MProvable m (SArray a b -> p) where
  argReduce k = newArray_ Nothing >>= \a -> argReduce $ k a

-- 2 Tuple
instance (SymVal a, SymVal b, MProvable m p) => MProvable m ((SBV a, SBV b) -> p) where
  argReduce k = mkArg >>= \a -> argReduce $ \b -> k (a, b)

-- 3 Tuple
instance (SymVal a, SymVal b, SymVal c, MProvable m p) => MProvable m ((SBV a, SBV b, SBV c) -> p) where
  argReduce k = mkArg >>= \a -> argReduce $ \b c -> k (a, b, c)

-- 4 Tuple
instance (SymVal a, SymVal b, SymVal c, SymVal d, MProvable m p) => MProvable m ((SBV a, SBV b, SBV c, SBV d) -> p) where
  argReduce k = mkArg  >>= \a -> argReduce $ \b c d -> k (a, b, c, d)

-- 5 Tuple
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, MProvable m p) => MProvable m ((SBV a, SBV b, SBV c, SBV d, SBV e) -> p) where
  argReduce k = mkArg >>= \a -> argReduce $ \b c d e -> k (a, b, c, d, e)

-- 6 Tuple
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, MProvable m p) => MProvable m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> p) where
  argReduce k = mkArg >>= \a -> argReduce $ \b c d e f -> k (a, b, c, d, e, f)

-- 7 Tuple
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, MProvable m p) => MProvable m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> p) where
  argReduce k = mkArg >>= \a -> argReduce $ \b c d e f g -> k (a, b, c, d, e, f, g)

-- | Generalization of 'Data.SBV.runSMT'
runSMT :: MonadIO m => SymbolicT m a -> m a
runSMT = runSMTWith defaultSMTCfg

-- | Generalization of 'Data.SBV.runSMTWith'
runSMTWith :: MonadIO m => SMTConfig -> SymbolicT m a -> m a
runSMTWith cfg a = fst <$> runSymbolic cfg (SMTMode QueryExternal ISetup True cfg) a

-- | Runs with a query.
runWithQuery :: MProvable m a => Bool -> QueryT m b -> SMTConfig -> a -> m b
runWithQuery isSAT q cfg a = fst <$> runSymbolic cfg (SMTMode QueryInternal ISetup isSAT cfg) comp
  where comp =  do _ <- argReduce a >>= output
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
