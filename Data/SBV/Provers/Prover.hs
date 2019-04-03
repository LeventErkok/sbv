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

module Data.SBV.Provers.Prover (
         SMTSolver(..), SMTConfig(..), Predicate
       , MProvable(..), Provable, proveWithAll, proveWithAny , satWithAll, satWithAny
       , generateSMTBenchmark
       , Goal
       , ThmResult(..), SatResult(..), AllSatResult(..), SafeResult(..), OptimizeResult(..), SMTResult(..)
       , SExecutable(..), isSafe
       , runSMT, runSMTWith
       , SatModel(..), Modelable(..), displayModels, extractModels
       , getModelDictionaries, getModelValues, getModelUninterpretedValues
       , boolector, cvc4, yices, z3, mathSAT, abc, defaultSMTCfg
       ) where


import Control.Monad          (when, unless)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.DeepSeq        (rnf, NFData(..))

import Control.Concurrent.Async (async, waitAny, asyncThreadId, Async)
import Control.Exception (finally, throwTo, AsyncException(ThreadKilled))

import System.IO.Unsafe (unsafeInterleaveIO)             -- only used safely!

import System.Directory  (getCurrentDirectory)

import Data.Time (getZonedTime, NominalDiffTime, UTCTime, getCurrentTime, diffUTCTime)
import Data.List (intercalate, isPrefixOf, nub)

import Data.Maybe (mapMaybe, listToMaybe)

import qualified Data.Map.Strict as M
import qualified Data.Foldable   as S (toList)

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

import qualified Data.SBV.Provers.Boolector  as Boolector
import qualified Data.SBV.Provers.CVC4       as CVC4
import qualified Data.SBV.Provers.Yices      as Yices
import qualified Data.SBV.Provers.Z3         as Z3
import qualified Data.SBV.Provers.MathSAT    as MathSAT
import qualified Data.SBV.Provers.ABC        as ABC

mkConfig :: SMTSolver -> SMTLibVersion -> [Control.SMTOption] -> SMTConfig
mkConfig s smtVersion startOpts = SMTConfig { verbose                     = False
                                            , timing                      = NoTiming
                                            , printBase                   = 10
                                            , printRealPrec               = 16
                                            , transcript                  = Nothing
                                            , solver                      = s
                                            , smtLibVersion               = smtVersion
                                            , satCmd                      = "(check-sat)"
                                            , satTrackUFs                 = True                   -- i.e., yes, do extract UI function values
                                            , allSatMaxModelCount         = Nothing                -- i.e., return all satisfying models
                                            , allSatPrintAlong            = False                  -- i.e., do not print models as they are found
                                            , isNonModelVar               = const False            -- i.e., everything is a model-variable by default
                                            , validateModel               = False
                                            , optimizeValidateConstraints = False
                                            , allowQuantifiedQueries      = False
                                            , roundingMode                = RoundNearestTiesToEven
                                            , solverSetOptions            = startOpts
                                            , ignoreExitCode              = False
                                            , redirectVerbose             = Nothing
                                            }

-- | If supported, this makes all output go to stdout, which works better with SBV
-- Alas, not all solvers support it..
allOnStdOut :: Control.SMTOption
allOnStdOut = Control.OptionKeyword ":diagnostic-output-channel" [show "stdout"]

-- | Default configuration for the Boolector SMT solver
boolector :: SMTConfig
boolector = mkConfig Boolector.boolector SMTLib2 []

-- | Default configuration for the CVC4 SMT Solver.
cvc4 :: SMTConfig
cvc4 = mkConfig CVC4.cvc4 SMTLib2 [allOnStdOut]

-- | Default configuration for the Yices SMT Solver.
yices :: SMTConfig
yices = mkConfig Yices.yices SMTLib2 []

-- | Default configuration for the Z3 SMT solver
z3 :: SMTConfig
z3 = mkConfig Z3.z3 SMTLib2 [ Control.OptionKeyword ":smtlib2_compliant" ["true"]
                            , allOnStdOut
                            ]

-- | Default configuration for the MathSAT SMT solver
mathSAT :: SMTConfig
mathSAT = mkConfig MathSAT.mathSAT SMTLib2 [allOnStdOut]

-- | Default configuration for the ABC synthesis and verification tool.
abc :: SMTConfig
abc = mkConfig ABC.abc SMTLib2 [allOnStdOut]

-- | The default solver used by SBV. This is currently set to z3.
defaultSMTCfg :: SMTConfig
defaultSMTCfg = z3

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
  -- | Generalization of 'Data.SBV.forAll_'
  forAll_ :: a -> SymbolicT m SBool

  -- | Generalization of 'Data.SBV.forAll'
  forAll  :: [String] -> a -> SymbolicT m SBool

  -- | Generalization of 'Data.SBV.forSome_'
  forSome_ :: a -> SymbolicT m SBool

  -- | Generalization of 'Data.SBV.forSome'
  forSome :: [String] -> a -> SymbolicT m SBool

  -- | Generalization of 'Data.SBV.prove'
  prove :: a -> m ThmResult
  prove = proveWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.proveWith'
  proveWith :: SMTConfig -> a -> m ThmResult
  proveWith cfg a = do r <- runWithQuery False (checkNoOptimizations >> Control.getSMTResult) cfg a
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

  -- | Generalization of 'Data.SBV.allSat'
  allSat :: a -> m AllSatResult
  allSat = allSatWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.allSatWith'
  allSatWith :: SMTConfig -> a -> m AllSatResult
  allSatWith cfg a = do f@(mm, pe, un, rs) <- runWithQuery True (checkNoOptimizations >> Control.getAllSatResult) cfg a
                        AllSatResult <$> if validationRequested cfg
                                         then do rs' <- mapM (validate True cfg a) rs
                                                 return (mm, pe, un, rs')
                                         else return f

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
                   qinps      <- Control.getQuantifiedInputs
                   spgm       <- Control.getSBVPgm

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


                   let universals = [s | (ALL, s) <- qinps]

                       firstUniversal
                         | null universals = error "Data.SBV: Impossible happened! Universal optimization with no universals!"
                         | True            = minimum (map (nodeId . fst) universals)

                       nodeId (SV _ n) = n

                       mappings :: M.Map SV SBVExpr
                       mappings = M.fromList (S.toList (pgmAssignments spgm))

                       chaseUniversal entry = map snd $ go entry []
                         where go x sofar
                                | nx >= firstUniversal
                                = nub $ [unm | unm@(u, _) <- universals, nx >= nodeId u] ++ sofar
                                | True
                                = let oVars (LkUp _ a b)             = [a, b]
                                      oVars (IEEEFP (FP_Cast _ _ o)) = [o]
                                      oVars _                        = []
                                      vars = case x `M.lookup` mappings of
                                               Nothing            -> []
                                               Just (SBVApp o ss) -> nub (oVars o ++ ss)
                                  in foldr go sofar vars
                                where nx = nodeId x

                   let needsUniversalOpt = let tag _  [] = Nothing
                                               tag nm xs = Just (nm, xs)
                                               needsUniversal (Maximize          nm (x, _))   = tag nm (chaseUniversal x)
                                               needsUniversal (Minimize          nm (x, _))   = tag nm (chaseUniversal x)
                                               needsUniversal (AssertWithPenalty nm (x, _) _) = tag nm (chaseUniversal x)
                                           in mapMaybe needsUniversal objectives

                   unless (null universals || null needsUniversalOpt) $
                          let len = maximum $ 0 : [length nm | (nm, _) <- needsUniversalOpt]
                              pad n = n ++ replicate (len - length n) ' '
                          in error $ unlines $ [ ""
                                               , "*** Data.SBV: Problem needs optimization of metric in the scope of universally quantified variable(s):"
                                               , "***"
                                               ]
                                           ++  [ "***          " ++  pad s ++ " [Depends on: " ++ intercalate ", " xs ++ "]"  | (s, xs) <- needsUniversalOpt ]
                                           ++  [ "***"
                                               , "*** Optimization is only meaningful with existentially quantified metrics."
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
       fst <$> runSymbolic (SMTMode QueryInternal ISetup True cfg) (forSome_ a >> Control.executeQuery QueryInternal check)
     where
       check :: QueryT m Bool
       check = do cs <- Control.checkSat
                  case cs of
                    Control.Unsat -> return True
                    Control.Sat   -> return False
                    Control.Unk   -> error "SBV: isVacuous: Solver returned unknown!"

  -- | Generalization of 'Data.SBV.isTheorem'
  isTheorem :: a -> m Bool
  isTheorem = isTheoremWith defaultSMTCfg

  -- | Generalization of 'Data.SBV.isTheoremWith'
  isTheoremWith :: SMTConfig -> a -> m Bool
  isTheoremWith cfg p = do r <- proveWith cfg p
                           case r of
                             ThmResult Unsatisfiable{} -> return True
                             ThmResult Satisfiable{}   -> return False
                             _                         -> error $ "SBV.isTheorem: Received:\n" ++ show r


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
                                                    Nothing  -> error "Data.SBV.validate: Impossible happaned; no bindings generated during model validation."
                                                    Just env -> check env
                               SatExtField{}   -> return $ ProofError cfg [ "The model requires an extension field value."
                                                                          , "Cannot validate models with infinities/epsilons produced during optimization."
                                                                          , ""
                                                                          , "To turn validation off, use `cfg{optimizeValidateConstraints = False}`"
                                                                          , ""
                                                                          , "Unable to validate the produced model."
                                                                          ]
                                                                          (Just res)
                               Unknown{}       -> return res
                               ProofError{}    -> return res

    where check env = do let envShown = showModelDictionary True True cfg modelBinds
                                where modelBinds = [(n, fake q s v) | ((q, (s, n)), v) <- env]
                                      fake q s Nothing
                                        | q == ALL
                                        = RegularCV $ CV (kindOf s) $ CUserSort (Nothing, "<universally quantified>")
                                        | True
                                        = RegularCV $ CV (kindOf s) $ CUserSort (Nothing, "<no binding found>")
                                      fake _ _ (Just v) = RegularCV v

                             notify s
                               | not (verbose cfg) = return ()
                               | True              = debug cfg ["[VALIDATE] " `alignPlain` s]

                         notify $ "Validating the model. " ++ if null env then "There are no assignments." else "Assignment:"
                         mapM_ notify ["    " ++ l | l <- lines envShown]

                         result <- snd <$> runSymbolic (Concrete (Just (isSAT, env))) ((if isSAT then forSome_ p else forAll_ p) >>= output)

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
                                                                          IEEEFP FP_FMA     -> Just "Floating point FMA operation is not supported concretely."
                                                                          IEEEFP _          -> Just "Not all floating point operations are supported concretely."
                                                                          OverflowOp _      -> Just "Overflow-checking is not done concretely."
                                                                          StrOp (StrInRe _) -> Just "Regular expression matches are not supported in validation mode."
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
-- Note that we send a @ThreadKilled@ to the losing processes, but we do *not* actually wait for them
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
-- Note that we send a @ThreadKilled@ to the losing processes, but we do *not* actually wait for them
-- to finish. In rare cases this can lead to zombie processes. In previous experiments, we found
-- that some processes take their time to terminate. So, this solution favors quick turnaround.
satWithAny :: Provable a => [SMTConfig] -> a -> IO (Solver, NominalDiffTime, SatResult)
satWithAny    = (`sbvWithAny` satWith)

-- | Create an SMT-Lib2 benchmark. The 'Bool' argument controls whether this is a SAT instance, i.e.,
-- translate the query directly, or a PROVE instance, i.e., translate the negated query.
generateSMTBenchmark :: (MonadIO m, MProvable m a) => Bool -> a -> m String
generateSMTBenchmark isSat a = do
      t <- liftIO getZonedTime

      let comments = ["Automatically created by SBV on " ++ show t]
          cfg      = defaultSMTCfg { smtLibVersion = SMTLib2 }

      (_, res) <- runSymbolic (SMTMode QueryInternal ISetup isSat cfg) $ (if isSat then forSome_ else forAll_) a >>= output

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

-- If we get a program producing nothing (i.e., Symbolic ()), pretend it simply returns True.
-- This is useful since min/max calls and constraints will provide the context
instance ExtractIO m => MProvable m (SymbolicT m ()) where
  forAll_    a = forAll_    ((a >> return sTrue) :: SymbolicT m SBool)
  forAll ns  a = forAll ns  ((a >> return sTrue) :: SymbolicT m SBool)
  forSome_   a = forSome_   ((a >> return sTrue) :: SymbolicT m SBool)
  forSome ns a = forSome ns ((a >> return sTrue) :: SymbolicT m SBool)

instance ExtractIO m => MProvable m (SymbolicT m SBool) where
  forAll_    = id
  forAll []  = id
  forAll xs  = error $ "SBV.forAll: Extra unmapped name(s) in predicate construction: " ++ intercalate ", " xs
  forSome_   = id
  forSome [] = id
  forSome xs = error $ "SBV.forSome: Extra unmapped name(s) in predicate construction: " ++ intercalate ", " xs

instance ExtractIO m => MProvable m SBool where
  forAll_   = return
  forAll _  = return
  forSome_  = return
  forSome _ = return

{-
-- The following works, but it lets us write properties that
-- are not useful.. Such as: prove $ \x y -> (x::SInt8) == y
-- Running that will throw an exception since Haskell's equality
-- is not be supported by symbolic things. (Needs .==).
instance Provable Bool where
  forAll_  x  = forAll_   (if x then true else false :: SBool)
  forAll s x  = forAll s  (if x then true else false :: SBool)
  forSome_  x = forSome_  (if x then true else false :: SBool)
  forSome s x = forSome s (if x then true else false :: SBool)
-}

-- Functions
instance (SymVal a, MProvable m p) => MProvable m (SBV a -> p) where
  forAll_        k = forall_   >>= \a -> forAll_   $ k a
  forAll (s:ss)  k = forall s  >>= \a -> forAll ss $ k a
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ k a
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ k a
  forSome []     k = forSome_ k

-- SFunArrays (memory, functional representation), only supported universally for the time being
instance (HasKind a, HasKind b, MProvable m p) => MProvable m (SArray a b -> p) where
  forAll_       k = newArray_  Nothing >>= \a -> forAll_   $ k a
  forAll (s:ss) k = newArray s Nothing >>= \a -> forAll ss $ k a
  forAll []     k = forAll_ k
  forSome_      _ = error "SBV.forSome.SFunArray: Existential arrays are not currently supported."
  forSome _     _ = error "SBV.forSome.SFunArray: Existential arrays are not currently supported."

-- SArrays (memory, SMT-Lib notion of arrays), only supported universally for the time being
instance (HasKind a, HasKind b, MProvable m p) => MProvable m (SFunArray a b -> p) where
  forAll_       k = newArray_  Nothing >>= \a -> forAll_   $ k a
  forAll (s:ss) k = newArray s Nothing >>= \a -> forAll ss $ k a
  forAll []     k = forAll_ k
  forSome_      _ = error "SBV.forSome.SArray: Existential arrays are not currently supported."
  forSome _     _ = error "SBV.forSome.SArray: Existential arrays are not currently supported."

-- 2 Tuple
instance (SymVal a, SymVal b, MProvable m p) => MProvable m ((SBV a, SBV b) -> p) where
  forAll_        k = forall_  >>= \a -> forAll_   $ \b -> k (a, b)
  forAll (s:ss)  k = forall s >>= \a -> forAll ss $ \b -> k (a, b)
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b -> k (a, b)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b -> k (a, b)
  forSome []     k = forSome_ k

-- 3 Tuple
instance (SymVal a, SymVal b, SymVal c, MProvable m p) => MProvable m ((SBV a, SBV b, SBV c) -> p) where
  forAll_       k  = forall_  >>= \a -> forAll_   $ \b c -> k (a, b, c)
  forAll (s:ss) k  = forall s >>= \a -> forAll ss $ \b c -> k (a, b, c)
  forAll []     k  = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b c -> k (a, b, c)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b c -> k (a, b, c)
  forSome []     k = forSome_ k

-- 4 Tuple
instance (SymVal a, SymVal b, SymVal c, SymVal d, MProvable m p) => MProvable m ((SBV a, SBV b, SBV c, SBV d) -> p) where
  forAll_        k = forall_  >>= \a -> forAll_   $ \b c d -> k (a, b, c, d)
  forAll (s:ss)  k = forall s >>= \a -> forAll ss $ \b c d -> k (a, b, c, d)
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b c d -> k (a, b, c, d)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b c d -> k (a, b, c, d)
  forSome []     k = forSome_ k

-- 5 Tuple
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, MProvable m p) => MProvable m ((SBV a, SBV b, SBV c, SBV d, SBV e) -> p) where
  forAll_        k = forall_  >>= \a -> forAll_   $ \b c d e -> k (a, b, c, d, e)
  forAll (s:ss)  k = forall s >>= \a -> forAll ss $ \b c d e -> k (a, b, c, d, e)
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b c d e -> k (a, b, c, d, e)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b c d e -> k (a, b, c, d, e)
  forSome []     k = forSome_ k

-- 6 Tuple
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, MProvable m p) => MProvable m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> p) where
  forAll_        k = forall_  >>= \a -> forAll_   $ \b c d e f -> k (a, b, c, d, e, f)
  forAll (s:ss)  k = forall s >>= \a -> forAll ss $ \b c d e f -> k (a, b, c, d, e, f)
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b c d e f -> k (a, b, c, d, e, f)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b c d e f -> k (a, b, c, d, e, f)
  forSome []     k = forSome_ k

-- 7 Tuple
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, MProvable m p) => MProvable m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> p) where
  forAll_        k = forall_  >>= \a -> forAll_   $ \b c d e f g -> k (a, b, c, d, e, f, g)
  forAll (s:ss)  k = forall s >>= \a -> forAll ss $ \b c d e f g -> k (a, b, c, d, e, f, g)
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b c d e f g -> k (a, b, c, d, e, f, g)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b c d e f g -> k (a, b, c, d, e, f, g)
  forSome []     k = forSome_ k

-- | Generalization of 'Data.SBV.runSMT'
runSMT :: MonadIO m => SymbolicT m a -> m a
runSMT = runSMTWith defaultSMTCfg

-- | Generalization of 'Data.SBV.runSMTWith'
runSMTWith :: MonadIO m => SMTConfig -> SymbolicT m a -> m a
runSMTWith cfg a = fst <$> runSymbolic (SMTMode QueryExternal ISetup True cfg) a

-- | Runs with a query.
runWithQuery :: MProvable m a => Bool -> QueryT m b -> SMTConfig -> a -> m b
runWithQuery isSAT q cfg a = fst <$> runSymbolic (SMTMode QueryInternal ISetup isSAT cfg) comp
  where comp =  do _ <- (if isSAT then forSome_ else forAll_) a >>= output
                   Control.executeQuery QueryInternal q

-- | Check if a safe-call was safe or not, turning a 'SafeResult' to a Bool.
isSafe :: SafeResult -> Bool
isSafe (SafeResult (_, _, result)) = case result of
                                       Unsatisfiable{} -> True
                                       Satisfiable{}   -> False
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
         cancelFast other = throwTo (asyncThreadId other) ThreadKilled

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

-- | Symbolically executable program fragments. This class is mainly used for 'safe' calls, and is sufficently populated internally to cover most use
-- cases. Users can extend it as they wish to allow 'safe' checks for SBV programs that return/take types that are user-defined.
class ExtractIO m => SExecutable m a where
   -- | Generalization of 'Data.SBV.sName_'
   sName_ :: a -> SymbolicT m ()
   -- | Generalization of 'Data.SBV.sName'
   sName  :: [String] -> a -> SymbolicT m ()

   -- | Generalization of 'Data.SBV.safe'
   safe :: a -> m [SafeResult]
   safe = safeWith defaultSMTCfg

   -- | Generalization of 'Data.SBV.safeWith'
   safeWith :: SMTConfig -> a -> m [SafeResult]
   safeWith cfg a = do cwd <- (++ "/") <$> liftIO getCurrentDirectory
                       let mkRelative path
                              | cwd `isPrefixOf` path = drop (length cwd) path
                              | True                  = path
                       fst <$> runSymbolic (SMTMode QueryInternal ISafe True cfg) (sName_ a >> check mkRelative)
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
   sName_   a = a >>= \r -> rnf r `seq` return ()
   sName []   = sName_
   sName xs   = error $ "SBV.SExecutable.sName: Extra unmapped name(s): " ++ intercalate ", " xs

instance ExtractIO m => SExecutable m (SBV a) where
   sName_   v = sName_   (output v :: SymbolicT m (SBV a))
   sName xs v = sName xs (output v :: SymbolicT m (SBV a))

-- Unit output
instance ExtractIO m => SExecutable m () where
   sName_   () = sName_   (output () :: SymbolicT m ())
   sName xs () = sName xs (output () :: SymbolicT m ())

-- List output
instance ExtractIO m => SExecutable m [SBV a] where
   sName_   vs = sName_   (output vs :: SymbolicT m [SBV a])
   sName xs vs = sName xs (output vs :: SymbolicT m [SBV a])

-- 2 Tuple output
instance (ExtractIO m, NFData a, SymVal a, NFData b, SymVal b) => SExecutable m (SBV a, SBV b) where
  sName_ (a, b) = sName_ (output a >> output b :: SymbolicT m (SBV b))
  sName _       = sName_

-- 3 Tuple output
instance (ExtractIO m, NFData a, SymVal a, NFData b, SymVal b, NFData c, SymVal c) => SExecutable m (SBV a, SBV b, SBV c) where
  sName_ (a, b, c) = sName_ (output a >> output b >> output c :: SymbolicT m (SBV c))
  sName _          = sName_

-- 4 Tuple output
instance (ExtractIO m, NFData a, SymVal a, NFData b, SymVal b, NFData c, SymVal c, NFData d, SymVal d) => SExecutable m (SBV a, SBV b, SBV c, SBV d) where
  sName_ (a, b, c, d) = sName_ (output a >> output b >> output c >> output c >> output d :: SymbolicT m (SBV d))
  sName _             = sName_

-- 5 Tuple output
instance (ExtractIO m, NFData a, SymVal a, NFData b, SymVal b, NFData c, SymVal c, NFData d, SymVal d, NFData e, SymVal e) => SExecutable m (SBV a, SBV b, SBV c, SBV d, SBV e) where
  sName_ (a, b, c, d, e) = sName_ (output a >> output b >> output c >> output d >> output e :: SymbolicT m (SBV e))
  sName _                = sName_

-- 6 Tuple output
instance (ExtractIO m, NFData a, SymVal a, NFData b, SymVal b, NFData c, SymVal c, NFData d, SymVal d, NFData e, SymVal e, NFData f, SymVal f) => SExecutable m (SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) where
  sName_ (a, b, c, d, e, f) = sName_ (output a >> output b >> output c >> output d >> output e >> output f :: SymbolicT m (SBV f))
  sName _                   = sName_

-- 7 Tuple output
instance (ExtractIO m, NFData a, SymVal a, NFData b, SymVal b, NFData c, SymVal c, NFData d, SymVal d, NFData e, SymVal e, NFData f, SymVal f, NFData g, SymVal g) => SExecutable m (SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) where
  sName_ (a, b, c, d, e, f, g) = sName_ (output a >> output b >> output c >> output d >> output e >> output f >> output g :: SymbolicT m (SBV g))
  sName _                      = sName_

-- Functions
instance (SymVal a, SExecutable m p) => SExecutable m (SBV a -> p) where
   sName_        k = exists_   >>= \a -> sName_   $ k a
   sName (s:ss)  k = exists s  >>= \a -> sName ss $ k a
   sName []      k = sName_ k

-- 2 Tuple input
instance (SymVal a, SymVal b, SExecutable m p) => SExecutable m ((SBV a, SBV b) -> p) where
  sName_        k = exists_  >>= \a -> sName_   $ \b -> k (a, b)
  sName (s:ss)  k = exists s >>= \a -> sName ss $ \b -> k (a, b)
  sName []      k = sName_ k

-- 3 Tuple input
instance (SymVal a, SymVal b, SymVal c, SExecutable m p) => SExecutable m ((SBV a, SBV b, SBV c) -> p) where
  sName_       k  = exists_  >>= \a -> sName_   $ \b c -> k (a, b, c)
  sName (s:ss) k  = exists s >>= \a -> sName ss $ \b c -> k (a, b, c)
  sName []     k  = sName_ k

-- 4 Tuple input
instance (SymVal a, SymVal b, SymVal c, SymVal d, SExecutable m p) => SExecutable m ((SBV a, SBV b, SBV c, SBV d) -> p) where
  sName_        k = exists_  >>= \a -> sName_   $ \b c d -> k (a, b, c, d)
  sName (s:ss)  k = exists s >>= \a -> sName ss $ \b c d -> k (a, b, c, d)
  sName []      k = sName_ k

-- 5 Tuple input
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SExecutable m p) => SExecutable m ((SBV a, SBV b, SBV c, SBV d, SBV e) -> p) where
  sName_        k = exists_  >>= \a -> sName_   $ \b c d e -> k (a, b, c, d, e)
  sName (s:ss)  k = exists s >>= \a -> sName ss $ \b c d e -> k (a, b, c, d, e)
  sName []      k = sName_ k

-- 6 Tuple input
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SExecutable m p) => SExecutable m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> p) where
  sName_        k = exists_  >>= \a -> sName_   $ \b c d e f -> k (a, b, c, d, e, f)
  sName (s:ss)  k = exists s >>= \a -> sName ss $ \b c d e f -> k (a, b, c, d, e, f)
  sName []      k = sName_ k

-- 7 Tuple input
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, SExecutable m p) => SExecutable m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> p) where
  sName_        k = exists_  >>= \a -> sName_   $ \b c d e f g -> k (a, b, c, d, e, f, g)
  sName (s:ss)  k = exists s >>= \a -> sName ss $ \b c d e f g -> k (a, b, c, d, e, f, g)
  sName []      k = sName_ k

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
