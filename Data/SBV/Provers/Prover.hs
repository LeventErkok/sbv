
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
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Data.SBV.Provers.Prover (
         SMTSolver(..), SMTConfig(..), Predicate, Provable(..), Goal
       , ThmResult(..), SatResult(..), AllSatResult(..), SafeResult(..), OptimizeResult(..), SMTResult(..)
       , isSatisfiable, isSatisfiableWith, isTheorem, isTheoremWith
       , prove, proveWith
       , sat, satWith
       , allSat, allSatWith
       , safe, safeWith, isSafe
       , runSMT, runSMTWith, query
       , optimize, optimizeWith
       , isVacuous, isVacuousWith
       , SatModel(..), Modelable(..), displayModels, extractModels
       , getModelDictionaries, getModelValues, getModelUninterpretedValues
       , boolector, cvc4, yices, z3, mathSAT, abc, defaultSMTCfg
       , compileToSMTLib, generateSMTBenchmarks
       ) where

import Data.List (intercalate)

import Control.Monad        (when, unless)
import Control.Monad.Reader (ask)
import Control.Monad.Trans  (liftIO)
import Control.Monad.State  (evalStateT)

import System.FilePath   (addExtension)
import Data.Time         (getZonedTime)

import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic
import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib
import Data.SBV.Utils.TDiff

import Data.IORef (readIORef, writeIORef)

import qualified Data.SBV.Control       as Control
import qualified Data.SBV.Control.Query as Control
import qualified Data.SBV.Control.Utils as Control

import Control.DeepSeq (rnf)

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
z3 = cfg { solverSetOptions = solverSetOptions cfg ++ [Control.OptionKeyword ":pp.decimal_precision" [show (printRealPrec cfg)]] }
  where cfg = mkConfig Z3.z3 SMTLib2 [ Control.OptionKeyword ":smtlib2_compliant"    ["true"]
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
  -- | Version of 'forSome' that allows user defined names
  forSome :: [String] -> a -> Predicate

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

-- | Run an arbitrary symbolic computation, equivalent to @'runSMTWith' 'defaultSMTCfg''@
runSMT :: Symbolic a -> IO a
runSMT = runSMTWith defaultSMTCfg

-- | Prove a predicate, equivalent to @'proveWith' 'defaultSMTCfg'@
prove :: Provable a => a -> IO ThmResult
prove = proveWith defaultSMTCfg

-- | Find a satisfying assignment for a predicate, equivalent to @'satWith' 'defaultSMTCfg'@
sat :: Provable a => a -> IO SatResult
sat = satWith defaultSMTCfg

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
allSat :: Provable a => a -> IO AllSatResult
allSat = allSatWith defaultSMTCfg

-- | Optimize a given collection of `Objective`s
optimize :: Provable a => OptimizeStyle -> a -> IO OptimizeResult
optimize = optimizeWith defaultSMTCfg

-- | Check that all the 'sAssert' calls are safe, equivalent to @'safeWith' 'defaultSMTCfg'@
safe :: SExecutable a => a -> IO [SafeResult]
safe = safeWith defaultSMTCfg

-- | Check if the given constraints are satisfiable, equivalent to @'isVacuousWith' 'defaultSMTCfg'@.
-- See the function 'constrain' for an example use of 'isVacuous'. Also see the 'CheckConstrVacuity'
-- tactic.
isVacuous :: Provable a => a -> IO Bool
isVacuous = isVacuousWith defaultSMTCfg

-- | Check whether a given property is a theorem.
isTheoremWith :: Provable a => SMTConfig -> a -> IO Bool
isTheoremWith cfg p = do r <- proveWith cfg p
                         case r of
                           ThmResult Unsatisfiable{} -> return True
                           ThmResult Satisfiable{}   -> return False
                           _                         -> error $ "SBV.isTheorem: Received:\n" ++ show r

-- | Check whether a given property is satisfiable.
isSatisfiableWith :: Provable a => SMTConfig -> a -> IO Bool
isSatisfiableWith cfg p = do r <- satWith cfg p
                             case r of
                               SatResult Satisfiable{}   -> return True
                               SatResult Unsatisfiable{} -> return False
                               _                         -> error $ "SBV.isSatisfiable: Received: " ++ show r

-- | Checks theoremhood.
isTheorem :: Provable a => a -> IO Bool
isTheorem = isTheoremWith defaultSMTCfg

-- | Checks satisfiability.
isSatisfiable :: Provable a => a -> IO Bool
isSatisfiable = isSatisfiableWith defaultSMTCfg

-- | Compiles to SMT-Lib and returns the resulting program as a string. Useful for saving
-- the result to a file for off-line analysis, for instance if you have an SMT solver that's not natively
-- supported out-of-the box by the SBV library. It takes two arguments:
--
--    * version: The SMTLib-version to produce. Note that we currently only support SMTLib2.
--
--    * isSat  : If 'True', will translate it as a SAT query, i.e., in the positive. If 'False', will
--               translate as a PROVE query, i.e., it will negate the result. (In this case, the check-sat
--               call to the SMT solver will produce UNSAT if the input is a theorem, as usual.)
compileToSMTLib :: Provable a => SMTLibVersion   -- ^ Version of SMTLib to compile to. (Only SMTLib2 supported currently.)
                              -> Bool            -- ^ If True, translate directly, otherwise negate the goal. (Use True for SAT queries, False for PROVE queries.)
                              -> a
                              -> IO String
compileToSMTLib version isSat a = do
        t <- getZonedTime
        let comments = ["Automatically created by SBV on " ++ show t]
            cfg      = defaultSMTCfg { smtLibVersion = version }
        res <- runSymbolic (isSat, cfg) $ (if isSat then forSome_ else forAll_) a >>= output
        let SMTProblem{smtLibPgm} = runProofOn cfg isSat comments res
            out = show (smtLibPgm cfg NoCase)
        return $ out ++ "\n(check-sat)\n"

-- | Create SMT-Lib benchmarks, for supported versions of SMTLib. The first argument is the basename of the file.
-- The 'Bool' argument controls whether this is a SAT instance, i.e., translate the query
-- directly, or a PROVE instance, i.e., translate the negated query. (See the second boolean argument to
-- 'compileToSMTLib' for details.)
generateSMTBenchmarks :: Provable a => Bool -> FilePath -> a -> IO ()
generateSMTBenchmarks isSat f a = mapM_ gen [minBound .. maxBound]
  where gen v = do s <- compileToSMTLib v isSat a
                   let fn = f `addExtension` smtLibVersionExtension v
                   writeFile fn s
                   putStrLn $ "Generated " ++ show v ++ " benchmark " ++ show fn ++ "."

-- | Runs an arbitrary symbolic computation, exposed to the user in SAT mode
runSMTWith :: SMTConfig -> Symbolic a -> IO a
runSMTWith cfg a = fst <$> runSymbolicWithResult (SMTMode ISetup True cfg) a

-- | Runs with a query.
runWithQuery :: Provable a => Bool -> Query b -> SMTConfig -> a -> IO b
runWithQuery isSAT q cfg a = fst <$> runSymbolicWithResult (SMTMode ISetup isSAT cfg) comp
  where comp =  do _ <- (if isSAT then forSome_ else forAll_) a >>= output
                   query q

-- | Proves the predicate using the given SMT-solver
proveWith :: Provable predicate => SMTConfig -> predicate -> IO ThmResult
proveWith = runWithQuery False $ ThmResult <$> Control.getSMTResult

-- | Find a satisfying assignment using the given SMT-solver
satWith :: Provable a => SMTConfig -> a -> IO SatResult
satWith = runWithQuery True $ SatResult <$> Control.getSMTResult

-- | Optimizes the objectives using the given SMT-solver
optimizeWith :: Provable a => SMTConfig -> OptimizeStyle -> a -> IO OptimizeResult
optimizeWith config style = runWithQuery True opt config
  where opt = do objectives <- Control.getObjectives
                 qinps      <- Control.getQuantifiedInputs

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

                 let needsUniversalOpt = let universals = [s | (ALL, (s, _)) <- qinps]
                                             check (x, y) nm = [nm | any (`elem` universals) [x, y]]
                                             isUniversal (Maximize   nm xy)   = check xy nm
                                             isUniversal (Minimize   nm xy)   = check xy nm
                                             isUniversal (AssertSoft nm xy _) = check xy nm
                                         in  concatMap isUniversal objectives

                 unless (null needsUniversalOpt) $
                        error $ unlines [ ""
                                        , "*** Data.SBV: Problem needs optimization of universally quantified metric(s):"
                                        , "***"
                                        , "***          " ++  unwords needsUniversalOpt
                                        , "***"
                                        , "*** Optimization is only meaningful existentially quantified values."
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

-- | Check if any of the assertions can be violated
safeWith :: SExecutable a => SMTConfig -> a -> IO [SafeResult]
safeWith cfg a = fst <$> runSymbolicWithResult (SMTMode ISetup True cfg) (sName_ a >> check)
  where check = query $ Control.getSBVAssertions >>= mapM verify

        -- check that the cond is unsatisfiable. If satisfiable, that would
        -- indicate the assignment under which the 'sAssert' would fail
        verify :: (String, Maybe CallStack, SW) -> Query SafeResult
        verify (msg, cs, cond) = do
                let locInfo ps = let loc (f, sl) = concat [srcLocFile sl, ":", show (srcLocStartLine sl), ":", show (srcLocStartCol sl), ":", f] in intercalate ",\n " (map loc ps)
                    location   = (locInfo . getCallStack) `fmap` cs

                result <- do Control.push 1
                             Control.send True $ "(assert " ++ show cond ++ ")"
                             r <- Control.getSMTResult
                             Control.pop 1
                             return r

                return $ SafeResult (location, msg, result)

-- | Check if a safe-call was safe or not, turning a 'SafeResult' to a Bool.
isSafe :: SafeResult -> Bool
isSafe (SafeResult (_, _, result)) = case result of
                                       Unsatisfiable{} -> True
                                       Satisfiable{}   -> False
                                       SatExtField{}   -> False   -- conservative
                                       Unknown{}       -> False   -- conservative
                                       ProofError{}    -> False   -- conservative

-- | Determine if the constraints are vacuous using the given SMT-solver. Also see
-- the 'CheckConstrVacuity' tactic.
isVacuousWith :: Provable a => SMTConfig -> a -> IO Bool
isVacuousWith cfg a = fst <$> runSymbolicWithResult (SMTMode ISetup True cfg) (forSome_ a >> query check)  -- NB. Can't call runWithQuery since last constraint would become the implication!
   where check = do cs <- Control.checkSat
                    case cs of
                      Control.Unsat -> return True
                      Control.Sat   -> return False
                      Control.Unk   -> error "SBV: isVacuous: Solver returned unknown!"

-- | Find all satisfying assignments using the given SMT-solver
allSatWith :: Provable a => SMTConfig -> a -> IO AllSatResult
allSatWith = runWithQuery True $ AllSatResult <$> Control.getAllSatResult

runProofOn :: SMTConfig -> Bool -> [String] -> Result -> SMTProblem
runProofOn config isSat comments res@(Result ki _qcInfo _codeSegs is consts tbls arrs uis axs pgm cstrs tacs options goals assertions outputs) =
     let flipQ (ALL, x) = (EX,  x)
         flipQ (EX,  x) = (ALL, x)

         skolemize :: [(Quantifier, NamedSymVar)] -> [Either SW (SW, [SW])]
         skolemize quants = go quants ([], [])
           where go []                   (_,  sofar) = reverse sofar
                 go ((ALL, (v, _)):rest) (us, sofar) = go rest (v:us, Left v : sofar)
                 go ((EX,  (v, _)):rest) (us, sofar) = go rest (us,   Right (v, reverse us) : sofar)

         qinps      = if isSat then is else map flipQ is
         skolemMap  = skolemize qinps

         o = case outputs of
               []  -> trueSW
               [so] -> case so of
                        SW KBool _ -> so
                        _          -> trueSW
                                      {-
                                      -- TODO: We used to error out here, but "safeWith" might have a non-bool out
                                      -- I wish we can get rid of this and still check for it. Perhaps this entire
                                      -- runProofOn might disappear.
                                      error $ unlines [ "Impossible happened, non-boolean output: " ++ show so
                                                      , "Detected while generating the trace:\n" ++ show res
                                                      ]
                                      -}
               os  -> error $ unlines [ "User error: Multiple output values detected: " ++ show os
                                      , "Detected while generating the trace:\n" ++ show res
                                      , "*** Check calls to \"output\", they are typically not needed!"
                                      ]

         smtScript = toSMTLib config ki isSat comments is skolemMap consts tbls arrs uis axs pgm cstrs o
         problem   = SMTProblem { smtInputs=is, smtSkolemMap=skolemMap, kindsUsed=ki
                                , smtAsserts=assertions, tactics=tacs, smtOptions=options, objectives=goals, smtLibPgm=smtScript}

     in rnf problem `seq` problem

-- | Run a custom query
query :: Query a -> Symbolic a
query (Query userQuery) = do
     st <- ask
     rm <- liftIO $ readIORef (runMode st)
     case rm of
        -- Transitioning from setup
        SMTMode ISetup isSAT cfg -> liftIO $ do let backend = engine (solver cfg)

                                                res <- extractSymbolicSimulationState st

                                                let SMTProblem{smtOptions, smtLibPgm} = runProofOn cfg isSAT [] res
                                                    cfg' = cfg { solverSetOptions = solverSetOptions cfg ++ smtOptions }
                                                    pgm  = smtLibPgm cfg' NoCase

                                                writeIORef (runMode st) $ SMTMode IRun isSAT cfg

                                                backend cfg' st (show pgm) $ evalStateT userQuery

        -- Already in a query, in theory we can just continue, but that causes use-case issues
        -- so we reject it. TODO: Review if we should actually support this. The issue arises with
        -- expressions like this:
        --
        -- In the following t0's output doesn't get recorded, as the output call is too late when we get
        -- here. (The output field isn't "incremental.") So, t0/t1 behave differently!
        --
        --   t0 = satWith z3{verbose=True, transcript=Just "t.smt2"} $ query (return (false::SBool))
        --   t1 = satWith z3{verbose=True, transcript=Just "t.smt2"} $ ((return (false::SBool)) :: Predicate)
        --
        -- Also, not at all clear what it means to go in an out of query mode:
        --
        -- r = runSMTWith z3{verbose=True} $ do
        --         a' <- sInteger "a"
        --
        --        (a, av) <- query $ do _ <- checkSat
        --                              av <- getValue a'
        --                              return (a', av)
        --
        --        liftIO $ putStrLn $ "Got: " ++ show av
        --        -- constrain $ a .> literal av + 1      -- Cant' do this since we're "out" of query. Sigh.
        --
        --        bv <- query $ do constrain $ a .> literal av + 1
        --                         _ <- checkSat
        --                         getValue a
        --
        --        return $ a' .== a' + 1
        --
        -- This would be one possible implementation, alas it has the problems above:
        --
        --    SMTMode IRun _ _ -> liftIO $ evalStateT userQuery st
        --
        -- So, we just reject it.

        SMTMode IRun _ _ -> error $ unlines [ ""
                                            , "*** Data.SBV: Unsupported nested query is detected."
                                            , "***"
                                            , "*** Please group your queries into one block. Note that this"
                                            , "*** can also arise if you have a call to 'query' not within 'runSMT'"
                                            , "*** For instance, within 'sat'/'prove' calls with custom user queries."
                                            , "*** The solution is to do the sat/prove part in the query directly."
                                            , "***"
                                            , "*** While multiple/nested queries should not be necessary in general,"
                                            , "*** please do get in touch if your use case does require such a feature,"
                                            , "*** to see how we can accommodate such scenarios."
                                            ]

        -- Otherwise choke!
        m -> error $ unlines [ ""
                             , "*** Data.SBV: Invalid query call."
                             , "***"
                             , "***   Current mode: " ++ show m
                             , "***"
                             , "*** Query calls are only valid within runSMT/runSMTWith calls"
                             ]

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
