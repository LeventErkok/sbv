-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.Prover
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Provable abstraction and the connection to SMT solvers
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                  #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Data.SBV.Provers.Prover (
         SMTSolver(..), SMTConfig(..), Predicate, Provable(..), Goal
       , ThmResult(..), SatResult(..), AllSatResult(..), SafeResult(..), OptimizeResult(..), SMTResult(..)
       , SExecutable(..), isSafe
       , runSMT, runSMTWith
       , SatModel(..), Modelable(..), displayModels, extractModels
       , getModelDictionaries, getModelValues, getModelUninterpretedValues
       , boolector, cvc4, yices, z3, mathSAT, abc, defaultSMTCfg
       ) where


import Control.Monad   (when, unless)
import Control.DeepSeq (rnf, NFData(..))

import Control.Concurrent.Async (async, waitAny, asyncThreadId, Async)
import Control.Exception (finally, throwTo, AsyncException(ThreadKilled))

import System.IO.Unsafe (unsafeInterleaveIO)             -- only used safely!

import System.Directory  (getCurrentDirectory)

import Data.Time (getZonedTime, NominalDiffTime, UTCTime, getCurrentTime, diffUTCTime)
import Data.List (intercalate, isPrefixOf, nub)

import Data.Maybe (mapMaybe)

import qualified Data.Map.Strict as M
import qualified Data.Foldable   as S (toList)

import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic
import Data.SBV.SMT.SMT
import Data.SBV.Utils.TDiff

import qualified Data.SBV.Control       as Control
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
mkConfig s smtVersion startOpts = SMTConfig { verbose             = False
                                            , timing              = NoTiming
                                            , printBase           = 10
                                            , printRealPrec       = 16
                                            , transcript          = Nothing
                                            , solver              = s
                                            , smtLibVersion       = smtVersion
                                            , satCmd              = "(check-sat)"
                                            , allSatMaxModelCount = Nothing                -- i.e., return all satisfying models
                                            , isNonModelVar       = const False            -- i.e., everything is a model-variable by default
                                            , roundingMode        = RoundNearestTiesToEven
                                            , solverSetOptions    = startOpts
                                            , ignoreExitCode      = False
                                            , redirectVerbose     = Nothing
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
class Provable a where
  -- | Turns a value into a universally quantified predicate, internally naming the inputs.
  -- In this case the sbv library will use names of the form @s1, s2@, etc. to name these variables
  -- Example:
  --
  -- >  forAll_ $ \(x::SWord8) y -> x `shiftL` 2 .== y
  --
  -- is a predicate with two arguments, captured using an ordinary Haskell function. Internally,
  -- @x@ will be named @s0@ and @y@ will be named @s1@.
  forAll_ :: a -> Predicate

  -- | Turns a value into a predicate, allowing users to provide names for the inputs.
  -- If the user does not provide enough number of names for the variables, the remaining ones
  -- will be internally generated. Note that the names are only used for printing models and has no
  -- other significance; in particular, we do not check that they are unique. Example:
  --
  -- >  forAll ["x", "y"] $ \(x::SWord8) y -> x `shiftL` 2 .== y
  --
  -- This is the same as above, except the variables will be named @x@ and @y@ respectively,
  -- simplifying the counter-examples when they are printed.
  forAll  :: [String] -> a -> Predicate

  -- | Turns a value into an existentially quantified predicate. (Indeed, 'exists' would have been
  -- a better choice here for the name, but alas it's already taken.)
  forSome_ :: a -> Predicate

  -- | Version of 'forSome' that allows user defined names.
  forSome :: [String] -> a -> Predicate

  -- | Prove a predicate, using the default solver.
  prove :: a -> IO ThmResult
  prove = proveWith defaultSMTCfg

  -- | Prove the predicate using the given SMT-solver.
  proveWith :: SMTConfig -> a -> IO ThmResult
  proveWith = runWithQuery False $ ThmResult <$> Control.getSMTResult

  -- | Find a satisfying assignment for a predicate, using the default solver.
  sat :: a -> IO SatResult
  sat = satWith defaultSMTCfg

  -- | Find a satisfying assignment using the given SMT-solver.
  satWith :: SMTConfig -> a -> IO SatResult
  satWith = runWithQuery True $ SatResult <$> Control.getSMTResult

  -- | Find all satisfying assignments, using the default solver. See 'allSatWith' for details.
  allSat :: a -> IO AllSatResult
  allSat = allSatWith defaultSMTCfg

  -- | Return all satisfying assignments for a predicate, equivalent to @'allSatWith' 'defaultSMTCfg'@.
  -- Note that this call will block until all satisfying assignments are found. If you have a problem
  -- with infinitely many satisfying models (consider 'SInteger') or a very large number of them, you
  -- might have to wait for a long time. To avoid such cases, use the 'allSatMaxModelCount' parameter
  -- in the configuration.
  --
  -- NB. Uninterpreted constant/function values and counter-examples for array values are ignored for
  -- the purposes of @'allSat'@. That is, only the satisfying assignments modulo uninterpreted functions and
  -- array inputs will be returned. This is due to the limitation of not having a robust means of getting a
  -- function counter-example back from the SMT solver.
  --  Find all satisfying assignments using the given SMT-solver
  allSatWith :: SMTConfig -> a -> IO AllSatResult
  allSatWith = runWithQuery True $ AllSatResult <$> Control.getAllSatResult

  -- | Optimize a given collection of `Objective`s
  optimize :: OptimizeStyle -> a -> IO OptimizeResult
  optimize = optimizeWith defaultSMTCfg

  -- | Optimizes the objectives using the given SMT-solver.
  optimizeWith :: SMTConfig -> OptimizeStyle -> a -> IO OptimizeResult
  optimizeWith config style = runWithQuery True opt config
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

                   let universals = [s | (ALL, s) <- qinps]

                       firstUniversal
                         | null universals = error "Data.SBV: Impossible happened! Universal optimization with no universals!"
                         | True            = minimum (map (nodeId . fst) universals)

                       nodeId (SW _ n) = n

                       mappings :: M.Map SW SBVExpr
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
                                               needsUniversal (Maximize   nm (x, _))   = tag nm (chaseUniversal x)
                                               needsUniversal (Minimize   nm (x, _))   = tag nm (chaseUniversal x)
                                               needsUniversal (AssertSoft nm (x, _) _) = tag nm (chaseUniversal x)
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
                               minmax (Minimize   _  xy@(_, v))     = [mkEq xy, "(minimize "    ++ show v ++ ")"]
                               minmax (Maximize   _  xy@(_, v))     = [mkEq xy, "(maximize "    ++ show v ++ ")"]
                               minmax (AssertSoft nm xy@(_, v) mbp) = [mkEq xy, "(assert-soft " ++ show v ++ penalize mbp ++ ")"]
                                 where penalize DefaultPenalty    = ""
                                       penalize (Penalty w mbGrp)
                                          | w <= 0         = error $ unlines [ "SBV.AssertSoft: Goal " ++ show nm ++ " is assigned a non-positive penalty: " ++ shw
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

  -- | Check if the constraints given are consistent, using the default solver.
  isVacuous :: a -> IO Bool
  isVacuous = isVacuousWith defaultSMTCfg

  -- | Determine if the constraints are vacuous using the given SMT-solver.
  isVacuousWith :: SMTConfig -> a -> IO Bool
  isVacuousWith cfg a = -- NB. Can't call runWithQuery since last constraint would become the implication!
                        fst <$> runSymbolic (SMTMode ISetup True cfg) (forSome_ a >> Control.query check)
     where check = do cs <- Control.checkSat
                      case cs of
                        Control.Unsat -> return True
                        Control.Sat   -> return False
                        Control.Unk   -> error "SBV: isVacuous: Solver returned unknown!"

  -- | Checks theoremhood using the default solver.
  isTheorem :: a -> IO Bool
  isTheorem = isTheoremWith defaultSMTCfg

  -- | Check whether a given property is a theorem.
  isTheoremWith :: SMTConfig -> a -> IO Bool
  isTheoremWith cfg p = do r <- proveWith cfg p
                           case r of
                             ThmResult Unsatisfiable{} -> return True
                             ThmResult Satisfiable{}   -> return False
                             _                         -> error $ "SBV.isTheorem: Received:\n" ++ show r


  -- | Checks satisfiability using the default solver.
  isSatisfiable :: a -> IO Bool
  isSatisfiable = isSatisfiableWith defaultSMTCfg

  -- | Check whether a given property is satisfiable.
  isSatisfiableWith :: SMTConfig -> a -> IO Bool
  isSatisfiableWith cfg p = do r <- satWith cfg p
                               case r of
                                 SatResult Satisfiable{}   -> return True
                                 SatResult Unsatisfiable{} -> return False
                                 _                         -> error $ "SBV.isSatisfiable: Received: " ++ show r

  -- | Prove a property with multiple solvers, running them in separate threads. The
  -- results will be returned in the order produced.
  proveWithAll :: [SMTConfig] -> a -> IO [(Solver, NominalDiffTime, ThmResult)]
  proveWithAll  = (`sbvWithAll` proveWith)

  -- | Prove a property with multiple solvers, running them in separate threads. Only
  -- the result of the first one to finish will be returned, remaining threads will be killed.
  -- Note that we send a @ThreadKilled@ to the losing processes, but we do *not* actually wait for them
  -- to finish. In rare cases this can lead to zombie processes. In previous experiments, we found
  -- that some processes take their time to terminate. So, this solution favors quick turnaround.
  proveWithAny :: [SMTConfig] -> a -> IO (Solver, NominalDiffTime, ThmResult)
  proveWithAny  = (`sbvWithAny` proveWith)

  -- | Find a satisfying assignment to a property with multiple solvers, running them in separate threads. The
  -- results will be returned in the order produced.
  satWithAll :: [SMTConfig] -> a -> IO [(Solver, NominalDiffTime, SatResult)]
  satWithAll = (`sbvWithAll` satWith)

  -- | Find a satisfying assignment to a property with multiple solvers, running them in separate threads. Only
  -- the result of the first one to finish will be returned, remaining threads will be killed.
  -- Note that we send a @ThreadKilled@ to the losing processes, but we do *not* actually wait for them
  -- to finish. In rare cases this can lead to zombie processes. In previous experiments, we found
  -- that some processes take their time to terminate. So, this solution favors quick turnaround.
  satWithAny :: [SMTConfig] -> a -> IO (Solver, NominalDiffTime, SatResult)
  satWithAny    = (`sbvWithAny` satWith)

  -- | Create an SMT-Lib2 benchmark. The 'Bool' argument controls whether this is a SAT instance, i.e.,
  -- translate the query directly, or a PROVE instance, i.e., translate the negated query.
  generateSMTBenchmark :: Bool -> a -> IO String
  generateSMTBenchmark isSat a = do
        t <- getZonedTime

        let comments = ["Automatically created by SBV on " ++ show t]
            cfg      = defaultSMTCfg { smtLibVersion = SMTLib2 }

        (_, res) <- runSymbolic (SMTMode ISetup isSat cfg) $ (if isSat then forSome_ else forAll_) a >>= output

        let SMTProblem{smtLibPgm} = Control.runProofOn cfg isSat comments res
            out                   = show (smtLibPgm cfg)

        return $ out ++ "\n(check-sat)\n"

instance Provable Predicate where
  forAll_    = id
  forAll []  = id
  forAll xs  = error $ "SBV.forAll: Extra unmapped name(s) in predicate construction: " ++ intercalate ", " xs
  forSome_   = id
  forSome [] = id
  forSome xs = error $ "SBV.forSome: Extra unmapped name(s) in predicate construction: " ++ intercalate ", " xs

instance Provable SBool where
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
instance (SymWord a, Provable p) => Provable (SBV a -> p) where
  forAll_        k = forall_   >>= \a -> forAll_   $ k a
  forAll (s:ss)  k = forall s  >>= \a -> forAll ss $ k a
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ k a
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ k a
  forSome []     k = forSome_ k

-- SFunArrays (memory, functional representation), only supported universally for the time being
instance (HasKind a, HasKind b, Provable p) => Provable (SArray a b -> p) where
  forAll_       k = declNewSArray (\t -> "array_" ++ show t) >>= \a -> forAll_   $ k a
  forAll (s:ss) k = declNewSArray (const s)                  >>= \a -> forAll ss $ k a
  forAll []     k = forAll_ k
  forSome_      _ = error "SBV.forSome: Existential arrays are not currently supported."
  forSome _     _ = error "SBV.forSome: Existential arrays are not currently supported."

-- SArrays (memory, SMT-Lib notion of arrays), only supported universally for the time being
instance (HasKind a, HasKind b, Provable p) => Provable (SFunArray a b -> p) where
  forAll_       k = declNewSFunArray Nothing >>= \a -> forAll_   $ k a
  forAll (_:ss) k = declNewSFunArray Nothing >>= \a -> forAll ss $ k a
  forAll []     k = forAll_ k
  forSome_      _ = error "SBV.forSome: Existential arrays are not currently supported."
  forSome _     _ = error "SBV.forSome: Existential arrays are not currently supported."

-- 2 Tuple
instance (SymWord a, SymWord b, Provable p) => Provable ((SBV a, SBV b) -> p) where
  forAll_        k = forall_  >>= \a -> forAll_   $ \b -> k (a, b)
  forAll (s:ss)  k = forall s >>= \a -> forAll ss $ \b -> k (a, b)
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b -> k (a, b)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b -> k (a, b)
  forSome []     k = forSome_ k

-- 3 Tuple
instance (SymWord a, SymWord b, SymWord c, Provable p) => Provable ((SBV a, SBV b, SBV c) -> p) where
  forAll_       k  = forall_  >>= \a -> forAll_   $ \b c -> k (a, b, c)
  forAll (s:ss) k  = forall s >>= \a -> forAll ss $ \b c -> k (a, b, c)
  forAll []     k  = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b c -> k (a, b, c)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b c -> k (a, b, c)
  forSome []     k = forSome_ k

-- 4 Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, Provable p) => Provable ((SBV a, SBV b, SBV c, SBV d) -> p) where
  forAll_        k = forall_  >>= \a -> forAll_   $ \b c d -> k (a, b, c, d)
  forAll (s:ss)  k = forall s >>= \a -> forAll ss $ \b c d -> k (a, b, c, d)
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b c d -> k (a, b, c, d)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b c d -> k (a, b, c, d)
  forSome []     k = forSome_ k

-- 5 Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, Provable p) => Provable ((SBV a, SBV b, SBV c, SBV d, SBV e) -> p) where
  forAll_        k = forall_  >>= \a -> forAll_   $ \b c d e -> k (a, b, c, d, e)
  forAll (s:ss)  k = forall s >>= \a -> forAll ss $ \b c d e -> k (a, b, c, d, e)
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b c d e -> k (a, b, c, d, e)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b c d e -> k (a, b, c, d, e)
  forSome []     k = forSome_ k

-- 6 Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, Provable p) => Provable ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> p) where
  forAll_        k = forall_  >>= \a -> forAll_   $ \b c d e f -> k (a, b, c, d, e, f)
  forAll (s:ss)  k = forall s >>= \a -> forAll ss $ \b c d e f -> k (a, b, c, d, e, f)
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b c d e f -> k (a, b, c, d, e, f)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b c d e f -> k (a, b, c, d, e, f)
  forSome []     k = forSome_ k

-- 7 Tuple
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, SymWord g, Provable p) => Provable ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> p) where
  forAll_        k = forall_  >>= \a -> forAll_   $ \b c d e f g -> k (a, b, c, d, e, f, g)
  forAll (s:ss)  k = forall s >>= \a -> forAll ss $ \b c d e f g -> k (a, b, c, d, e, f, g)
  forAll []      k = forAll_ k
  forSome_       k = exists_  >>= \a -> forSome_   $ \b c d e f g -> k (a, b, c, d, e, f, g)
  forSome (s:ss) k = exists s >>= \a -> forSome ss $ \b c d e f g -> k (a, b, c, d, e, f, g)
  forSome []     k = forSome_ k

-- | Run an arbitrary symbolic computation, equivalent to @'runSMTWith' 'defaultSMTCfg'@
runSMT :: Symbolic a -> IO a
runSMT = runSMTWith defaultSMTCfg

-- | Runs an arbitrary symbolic computation, exposed to the user in SAT mode
runSMTWith :: SMTConfig -> Symbolic a -> IO a
runSMTWith cfg a = fst <$> runSymbolic (SMTMode ISetup True cfg) a

-- | Runs with a query.
runWithQuery :: Provable a => Bool -> Query b -> SMTConfig -> a -> IO b
runWithQuery isSAT q cfg a = fst <$> runSymbolic (SMTMode ISetup isSAT cfg) comp
  where comp =  do _ <- (if isSAT then forSome_ else forAll_) a >>= output
                   Control.query q

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
class SExecutable a where
   sName_ :: a -> Symbolic ()
   sName  :: [String] -> a -> Symbolic ()

   -- | Check safety using the default solver.
   safe :: a -> IO [SafeResult]
   safe = safeWith defaultSMTCfg

   -- | Check if any of the 'sAssert' calls can be violated.
   safeWith :: SMTConfig -> a -> IO [SafeResult]
   safeWith cfg a = do cwd <- (++ "/") <$> getCurrentDirectory
                       let mkRelative path
                              | cwd `isPrefixOf` path = drop (length cwd) path
                              | True                  = path
                       fst <$> runSymbolic (SMTMode ISetup True cfg) (sName_ a >> check mkRelative)
     where check mkRelative = Control.query $ Control.getSBVAssertions >>= mapM (verify mkRelative)

           -- check that the cond is unsatisfiable. If satisfiable, that would
           -- indicate the assignment under which the 'sAssert' would fail
           verify :: (FilePath -> FilePath) -> (String, Maybe CallStack, SW) -> Query SafeResult
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

instance NFData a => SExecutable (Symbolic a) where
   sName_   a = a >>= \r -> rnf r `seq` return ()
   sName []   = sName_
   sName xs   = error $ "SBV.SExecutable.sName: Extra unmapped name(s): " ++ intercalate ", " xs

instance SExecutable (SBV a) where
   sName_   v = sName_ (output v)
   sName xs v = sName xs (output v)

-- Unit output
instance SExecutable () where
   sName_   () = sName_   (output ())
   sName xs () = sName xs (output ())

-- List output
instance SExecutable [SBV a] where
   sName_   vs = sName_   (output vs)
   sName xs vs = sName xs (output vs)

-- 2 Tuple output
instance (NFData a, SymWord a, NFData b, SymWord b) => SExecutable (SBV a, SBV b) where
  sName_ (a, b) = sName_ (output a >> output b)
  sName _       = sName_

-- 3 Tuple output
instance (NFData a, SymWord a, NFData b, SymWord b, NFData c, SymWord c) => SExecutable (SBV a, SBV b, SBV c) where
  sName_ (a, b, c) = sName_ (output a >> output b >> output c)
  sName _          = sName_

-- 4 Tuple output
instance (NFData a, SymWord a, NFData b, SymWord b, NFData c, SymWord c, NFData d, SymWord d) => SExecutable (SBV a, SBV b, SBV c, SBV d) where
  sName_ (a, b, c, d) = sName_ (output a >> output b >> output c >> output c >> output d)
  sName _             = sName_

-- 5 Tuple output
instance (NFData a, SymWord a, NFData b, SymWord b, NFData c, SymWord c, NFData d, SymWord d, NFData e, SymWord e) => SExecutable (SBV a, SBV b, SBV c, SBV d, SBV e) where
  sName_ (a, b, c, d, e) = sName_ (output a >> output b >> output c >> output d >> output e)
  sName _                = sName_

-- 6 Tuple output
instance (NFData a, SymWord a, NFData b, SymWord b, NFData c, SymWord c, NFData d, SymWord d, NFData e, SymWord e, NFData f, SymWord f) => SExecutable (SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) where
  sName_ (a, b, c, d, e, f) = sName_ (output a >> output b >> output c >> output d >> output e >> output f)
  sName _                   = sName_

-- 7 Tuple output
instance (NFData a, SymWord a, NFData b, SymWord b, NFData c, SymWord c, NFData d, SymWord d, NFData e, SymWord e, NFData f, SymWord f, NFData g, SymWord g) => SExecutable (SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) where
  sName_ (a, b, c, d, e, f, g) = sName_ (output a >> output b >> output c >> output d >> output e >> output f >> output g)
  sName _                      = sName_

-- Functions
instance (SymWord a, SExecutable p) => SExecutable (SBV a -> p) where
   sName_        k = exists_   >>= \a -> sName_   $ k a
   sName (s:ss)  k = exists s  >>= \a -> sName ss $ k a
   sName []      k = sName_ k

-- 2 Tuple input
instance (SymWord a, SymWord b, SExecutable p) => SExecutable ((SBV a, SBV b) -> p) where
  sName_        k = exists_  >>= \a -> sName_   $ \b -> k (a, b)
  sName (s:ss)  k = exists s >>= \a -> sName ss $ \b -> k (a, b)
  sName []      k = sName_ k

-- 3 Tuple input
instance (SymWord a, SymWord b, SymWord c, SExecutable p) => SExecutable ((SBV a, SBV b, SBV c) -> p) where
  sName_       k  = exists_  >>= \a -> sName_   $ \b c -> k (a, b, c)
  sName (s:ss) k  = exists s >>= \a -> sName ss $ \b c -> k (a, b, c)
  sName []     k  = sName_ k

-- 4 Tuple input
instance (SymWord a, SymWord b, SymWord c, SymWord d, SExecutable p) => SExecutable ((SBV a, SBV b, SBV c, SBV d) -> p) where
  sName_        k = exists_  >>= \a -> sName_   $ \b c d -> k (a, b, c, d)
  sName (s:ss)  k = exists s >>= \a -> sName ss $ \b c d -> k (a, b, c, d)
  sName []      k = sName_ k

-- 5 Tuple input
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SExecutable p) => SExecutable ((SBV a, SBV b, SBV c, SBV d, SBV e) -> p) where
  sName_        k = exists_  >>= \a -> sName_   $ \b c d e -> k (a, b, c, d, e)
  sName (s:ss)  k = exists s >>= \a -> sName ss $ \b c d e -> k (a, b, c, d, e)
  sName []      k = sName_ k

-- 6 Tuple input
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, SExecutable p) => SExecutable ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> p) where
  sName_        k = exists_  >>= \a -> sName_   $ \b c d e f -> k (a, b, c, d, e, f)
  sName (s:ss)  k = exists s >>= \a -> sName ss $ \b c d e f -> k (a, b, c, d, e, f)
  sName []      k = sName_ k

-- 7 Tuple input
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, SymWord g, SExecutable p) => SExecutable ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> p) where
  sName_        k = exists_  >>= \a -> sName_   $ \b c d e f g -> k (a, b, c, d, e, f, g)
  sName (s:ss)  k = exists s >>= \a -> sName ss $ \b c d e f g -> k (a, b, c, d, e, f, g)
  sName []      k = sName_ k

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
