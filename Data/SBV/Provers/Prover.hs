
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
       , internalSATCheck
       -- Only here temporarily. To be eliminated/reduced once we decide the tactic story
       , applyTactics, bufferSanity
       ) where

import Data.Char         (isSpace)
import Data.List         (intercalate)

import Control.Monad        (when, unless)
import Control.Monad.Reader (ask)
import Control.Monad.Trans  (liftIO)
import Control.Monad.State  (evalStateT)

import System.FilePath   (addExtension)
import Data.Time         (getCurrentTime, utcToLocalZonedTime)
import System.IO         (hGetBuffering, hSetBuffering, stdout, hFlush, BufferMode(..))

import Control.Concurrent.Async (async, wait, cancel, waitAny, Async)

import GHC.Stack.Compat
#if !MIN_VERSION_base(4,9,0)
import GHC.SrcLoc.Compat
#endif

import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic
import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib
import Data.SBV.Utils.TDiff

import qualified Data.SBV.Control       as Control
import qualified Data.SBV.Control.Query as Control
import qualified Data.SBV.Control.Utils as Control

import Control.DeepSeq (rnf)
import Control.Exception (bracket)

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
                                            , customQuery         = Nothing
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
        t <- utcToLocalZonedTime =<< getCurrentTime
        let comments = ["Created on " ++ show t]
            cfg      = defaultSMTCfg { smtLibVersion = version }
        (_, SMTProblem{smtLibPgm}) <- simulate cfg isSat comments a
        let out = show (smtLibPgm cfg NoCase)
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

-- | Make sure we're line-buffering if there's going to be parallel calls.
bufferSanity :: Bool -> IO a -> IO a
bufferSanity False a = a
bufferSanity True  a = bracket before after (const a)
  where before = do b <- hGetBuffering stdout
                    hSetBuffering stdout LineBuffering
                    return b
        after b = do hFlush stdout
                     hSetBuffering stdout b
                     hFlush stdout

-- | Runs an arbitrary symbolic computation, exposed to the user in SAT mode
runSMTWith :: SMTConfig -> Symbolic a -> IO a
runSMTWith cfg a = fst <$> runSymbolic' (SMTMode ISetup True cfg) a

-- | Runs with a query.
runWithQuery :: Provable a => Bool -> Query b -> SMTConfig -> a -> IO b
runWithQuery isSAT q cfg a = fst <$> runSymbolic' (SMTMode ISetup isSAT cfg) comp
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

-- | Apply the given tactics to a problem
applyTactics :: SMTConfig                                                                -- ^ Solver configuration
             -> State                                                                    -- ^ State in which we're running
             -> (Bool, Bool)                                                             -- ^ Are we a sat-problem? Do we have anything parallel going on? (Parallel-case split.)
             -> (SMTResult -> res, res -> SMTResult)                                     -- ^ Wrapper/unwrapper pair from result to SMT answer
             -> [(String, (String, SW))]                                                 -- ^ Level at which we are called. (In case of a nested case-split)
             -> [Control.SMTOption]                                                      -- ^ Options to set
             -> [Tactic SW]                                                              -- ^ Tactics active at this level
             -> [Objective (SW, SW)]                                                     -- ^ Optimization goals we have
             -> (SMTConfig -> State -> Maybe (OptimizeStyle, Int) -> CaseCond -> IO res) -- ^ The actual continuation at this point
             -> IO res
applyTactics cfgIn ctx (isSat, hasPar) (wrap, unwrap) levels smtOptions tactics objectives cont
   = do --
        -- TODO: The management of tactics here is quite adhoc. We should have a better story
        -- Currently, we:
        --
        --      - Perform optimization (which requires sat and no case-splitting)
        --      - Check for vacuity if asked
        --      - Do case-splitting
        --
        -- If we have more interesting tactics, we'll have to come up with a better "proof manager." The current
        -- code is sufficient, however, for the use cases we have now.

        -- check that if we have objectives, then we must be sat and there must be no case-splits
        when (hasObjectives && not isSat)     $ error "SBV: Optimization is only available for sat calls."
        when (hasObjectives && hasCaseSplits) $ error "SBV: Optimization and case-splits are not supported together."

        let mbOptInfo = Nothing

        if hasObjectives

           then cont finalConfig ctx mbOptInfo (Opt objectives)

           else do -- Check vacuity if asked. If result is Nothing, it means we're good to go.
                   mbRes <- if not shouldCheckConstrVacuity
                            then return Nothing
                            else constraintVacuityCheck isSat finalConfig ctx mbOptInfo (wrap, unwrap) cont

                   -- Do case split, if vacuity said continue
                   case mbRes of
                     Just r  -> return r
                     Nothing -> if null caseSplits
                                then cont finalConfig ctx mbOptInfo (CasePath (map (snd . snd) levels))
                                else caseSplit finalConfig ctx mbOptInfo shouldCheckCaseVacuity (parallelCase, hasPar) isSat (wrap, unwrap) levels smtOptions chatty cases cont

  where (caseSplits, checkCaseVacuity, parallelCases, checkConstrVacuity, checkUsing)
                = foldr (flip classifyTactics) ([], [], [], [], []) tactics

        classifyTactics (a, b, c, d, e) = \case
                    t@CaseSplit{}           -> (t:a,   b,   c,   d,   e)
                    t@CheckCaseVacuity{}    -> (  a, t:b,   c,   d,   e)
                    t@ParallelCase{}        -> (  a,   b, t:c,   d,   e)
                    t@CheckConstrVacuity{}  -> (  a,   b,   c, t:d,   e)
                    t@CheckUsing{}          -> (  a,   b,   c,   d, t:e)

        hasObjectives = not $ null objectives

        hasCaseSplits = not $ null cases

        parallelCase  = not $ null parallelCases

        shouldCheckCaseVacuity = case [b | CheckCaseVacuity b <- checkCaseVacuity] of
                                   [] -> True   -- default is to check-case-vacuity
                                   bs -> or bs  -- otherwise check vacuity if we're asked to do so

        -- for constraint vacuity, default is *not* to check; so a simple or suffices
        shouldCheckConstrVacuity = or [b | CheckConstrVacuity b <- checkConstrVacuity]

        (chatty, cases) = let (vs, css) = unzip [(v, cs) | CaseSplit v cs <- caseSplits] in (or (verbose cfgIn : vs), concat css)

        grabCheckUsing c = case [s | CheckUsing s <- checkUsing] of
                             []  -> c
                             [s] -> c {satCmd = "(check-sat-using " ++ s ++ ")"}
                             ss  -> c {satCmd = "(check-sat-using (then " ++ unwords ss ++ "))"}

        grabSetOptions c = c { solverSetOptions = smtOptions ++ solverSetOptions c }

        finalConfig = grabSetOptions . grabCheckUsing $ cfgIn

-- | Implements the "constraint vacuity check" tactic, making sure the calls to "constrain"
-- describe a satisfiable condition. Returns:
--
--    - Nothing if this is a SAT call, as that would be a weird thing to do (we only would care about constraint-vacuity in a proof context),
--    - Nothing if satisfiable: The world is OK, just keep moving
--    - ProofError if unsatisfiable. In this case we found that the constraints given are just bad!
--
-- NB. We'll do a SAT call even if there are *no* constraints! This is OK, as the call will be cheap; and this is an opt-in call. (i.e.,
-- the user asked us to do it explicitly.)
constraintVacuityCheck :: forall res.
                          Bool                                                                     -- ^ isSAT?
                       -> SMTConfig                                                                -- ^ config
                       -> State                                                                    -- ^ query state
                       -> Maybe (OptimizeStyle, Int)                                               -- ^ optimization info
                       -> (SMTResult -> res, res -> SMTResult)                                     -- ^ wrappers back and forth from final result
                       -> (SMTConfig -> State -> Maybe (OptimizeStyle, Int) -> CaseCond -> IO res) -- ^ continuation
                       -> IO (Maybe res)                                                           -- ^ result, wrapped in Maybe if vacuity fails
constraintVacuityCheck True  _      _   _ _              _ = return Nothing -- for a SAT check, vacuity is meaningless (what would be the point)?
constraintVacuityCheck False config ctx d (wrap, unwrap) f = do
               res <- f config ctx d CstrVac
               case unwrap res of
                 Satisfiable{} -> return Nothing
                 _             -> return $ Just $ wrap vacuityFailResult
  where vacuityFailResult = ProofError config [ "Constraint vacuity check failed."
                                              , "User given constraints are not satisfiable."
                                              ]

-- | Implements the case-split tactic. Works for both Sat and Proof, hence the quantification on @res@
caseSplit :: forall res.
             SMTConfig                                                                -- ^ Solver config
          -> State                                                                    -- ^ Query state
          -> Maybe (OptimizeStyle, Int)                                               -- ^ Are we optimizing?
          -> Bool                                                                     -- ^ Should we check vacuity of cases?
          -> (Bool, Bool)                                                             -- ^ Should we run the cases in parallel? Second bool: Is anything parallel going on?
          -> Bool                                                                     -- ^ True if we're sat solving
          -> (SMTResult -> res, res -> SMTResult)                                     -- ^ wrapper, unwrapper from sat/proof to the actual result
          -> [(String, (String, SW))]                                                 -- ^ Path condition as we reached here. (In a nested case split, First #, then actual name.)
          -> [Control.SMTOption]                                                      -- ^ Options to pass down
          -> Bool                                                                     -- ^ Should we be chatty on the case-splits?
          -> [(String, SW, [Tactic SW])]                                              -- ^ List of cases. Case name, condition, plus further tactics for nested case-splitting etc.
          -> (SMTConfig -> State -> Maybe (OptimizeStyle, Int) -> CaseCond -> IO res) -- ^ The "solver" once we provide it with a problem and a case
          -> IO res
caseSplit config ctx mbOptInfo checkVacuity (runParallel, hasPar) isSAT (wrap, unwrap) level smtOptions chatty cases cont
     | runParallel = goParallel tasks
     | True        = goSerial   tasks

  where tasks = zip caseNos cases

        lids = map fst level

        noOfCases = length cases
        casePad   = length (show noOfCases)

        tagLength = maximum $ map length $ "Coverage" : [s | (s, _, _) <- cases]
        showTag t = take tagLength (t ++ repeat ' ')

        shCaseId i = let si = show i in replicate (casePad - length si) ' ' ++ si

        caseNos = map shCaseId [(1::Int) .. ]

        tag tagChar = replicate 2 tagChar ++ replicate (2 * length level) tagChar

        mkCaseNameBase s i = "Case "     ++ intercalate "." (lids ++ [i]) ++ ": " ++ showTag s
        mkCovNameBase      = "Coverage " ++ replicate (casePad - 1) ' ' ++ "X"

        mkCaseName tagChar s i = tag tagChar ++ ' ' : mkCaseNameBase s i
        mkCovName  tagChar     = tag tagChar ++ ' ' : mkCovNameBase

        startCase :: Bool -> Maybe (String, String) -> IO ()
        startCase multi mbis
           | not chatty          = return ()
           | Just (i, s) <- mbis = printer $ mkCaseName tagChar s i ++ start
           | True                = printer $ mkCovName  tagChar     ++ start
           where line = multi || hasPar

                 printer | line = putStrLn
                         | True = putStr
                 tagChar | line = '>'
                         | True = '*'
                 start          = " [Started]"

        vacuityMsg :: Maybe Bool -> Bool -> (String, String) -> IO ()
        vacuityMsg mbGood multi (i, s)
           | not chatty = return ()
           | line       = putStrLn $ mkCaseName '=' s i ++ msg
           | True       = printer                          msg
           where line = multi || hasPar
                 printer
                   | failed = putStrLn
                   | True   = putStr
                 (failed, msg) = case mbGood of
                                   Nothing    -> (False, " [Vacuity Skipped]")
                                   Just True  -> (False, " [Vacuity OK]")
                                   Just False -> (True,  " [Vacuity Failed]")

        endCase :: Bool -> Maybe (String, String) -> String -> IO ()
        endCase multi mbis msg
           | not chatty          = return ()
           | not line            = putStrLn $ ' ' : msg
           | Just (i, s) <- mbis = putStrLn $ mkCaseName '<' s i ++ ' ' : msg
           | True                = putStrLn $ mkCovName  '<'     ++ ' ' : msg
           where line = multi || hasPar

        -----------------------------------------------------------------------------------------------------------------
        -- Serial case analysis
        -----------------------------------------------------------------------------------------------------------------
        goSerial :: [(String, (String, SW, [Tactic SW]))] -> IO res
        goSerial []
           -- At the end, we do a coverage call
           = do let multi = runParallel
                startCase multi Nothing
                res <- cont config ctx mbOptInfo (CaseCov (map (snd . snd) level) [c | (_, c, _) <- cases])
                decideSerial multi Nothing (unwrap res) (return res)
        goSerial ((i, (nm, cond, ts)):cs)
           -- Still going down, do a regular call
           = do let multi = not . null $ [() | CaseSplit{} <- ts]
                    mbis  = Just (i, nm)
                startCase multi mbis
                continue <- if isSAT   -- for a SAT check, vacuity is meaningless (what would be the point)?
                            then return True
                            else if checkVacuity
                                 then do res <- cont config ctx mbOptInfo (CaseVac (map (snd . snd) level) cond)
                                         case unwrap res of
                                           Satisfiable{} -> vacuityMsg (Just True)  multi (i, nm) >> return True
                                           _             -> vacuityMsg (Just False) multi (i, nm) >> return False
                                 else vacuityMsg Nothing  multi (i, nm) >> return True
                if continue
                   then do res <- applyTactics config ctx (isSAT, hasPar) (wrap, unwrap) (level ++ [(i, (nm, cond))]) smtOptions ts [] cont
                           decideSerial multi mbis (unwrap res) (goSerial cs)
                   else return $ wrap $ vacuityFailResult (i, nm)

        vacuityFailResult cur = ProofError config $ [ "Vacuity check failed."
                                                    , "Case constraint not satisfiable. Leading path:"
                                                    ]
                                                 ++ map ("    " ++) (align ([(i, n) | (i, (n, _)) <- level] ++ [cur]))
                                                 ++ ["HINT: Try \"CheckCaseVacuity False\" tactic to ignore case vacuity checks."]
          where align :: [(String, String)] -> [String]
                align path = map join cpath
                  where len = maximum (0 : map (length . fst) cpath)
                        join (c, n) = reverse (take len (reverse c ++ repeat ' ')) ++ ": " ++ n

                        cpath = [(intercalate "." (reverse ls), j) | (ls, j) <- cascade [] path]

                        trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace
                        cascade _     []              = []
                        cascade sofar ((i, j) : rest) = let new = trim i : sofar in (new, j) : cascade new rest

        decideSerial
         | isSAT = decideSerialSAT
         | True  = decideSerialProof

        -- short name
        diag Unsatisfiable{} = "[Unsatisfiable]"
        diag Satisfiable  {} = "[Satisfiable]"
        diag SatExtField  {} = "[Satisfiable in Field Extension]"
        diag Unknown      {} = "[Unknown]"
        diag ProofError   {} = "[ProofError]"
        diag TimeOut      {} = "[TimeOut]"

        -- If we're SAT, we stop at first satisfiable and report back. Otherwise continue.
        -- Note that we also stop if we get a ProofError, as that clearly is not OK
        decideSerialSAT :: Bool -> Maybe (String, String) -> SMTResult -> IO res -> IO res
        decideSerialSAT multi mbis r@Satisfiable{} _ = endCase multi mbis (diag r) >> return (wrap r)
        decideSerialSAT multi mbis r@ProofError{}  _ = endCase multi mbis (diag r) >> return (wrap r)
        decideSerialSAT multi mbis r               k = endCase multi mbis (diag r) >> k

        -- If we're Prove, we stop at first *not* unsatisfiable and report back. Otherwise continue.
        decideSerialProof :: Bool -> Maybe (String, String) -> SMTResult -> IO res -> IO res
        decideSerialProof multi mbis Unsatisfiable{} k = endCase multi mbis "[Proved]" >> k
        decideSerialProof multi mbis r               _ = endCase multi mbis "[Failed]" >> return (wrap r)

        -----------------------------------------------------------------------------------------------------------------
        -- Parallel case analysis
        -----------------------------------------------------------------------------------------------------------------
        goParallel :: [(String, (String, SW, [Tactic SW]))] -> IO res
        goParallel cs = do
             when chatty $ putStrLn $ topName '>' "[Starting]"

             -- Create the case claim:
             let mkTask (i, (nm, cond, ts)) =
                  let caseProof = do continue <- if isSAT   -- for a SAT check, vacuity is meaningless (what would be the point)?
                                                 then return True
                                                 else if checkVacuity
                                                      then do res <- cont config ctx mbOptInfo (CaseVac (map (snd . snd) level) cond)
                                                              case unwrap res of
                                                                Satisfiable{} -> return True
                                                                _             -> return False
                                                      else return True
                                     if continue
                                        then unwrap `fmap` applyTactics config ctx (isSAT, hasPar) (wrap, unwrap) (level ++ [(i, (nm, cond))]) smtOptions ts [] cont
                                        else return $ vacuityFailResult (i, nm)
                  in (mkCaseNameBase nm i, caseProof)

             -- Create the coverage claim
             let cov = unwrap `fmap` cont config ctx mbOptInfo (CaseCov (map (snd . snd) level) [c | (_, c, _) <- cases])

             (decidingTag, res) <- decideParallel $ map mkTask cs ++ [(mkCovNameBase, cov)]

             let trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

             let caseMsg
                  | isSAT = satMsg
                  | True  = proofMsg
                  where addTag x = x ++ " (at " ++ trim decidingTag ++ ")"
                        (satMsg, proofMsg) =  case res of
                                                Unsatisfiable{} -> ("[Unsatisfiable]", "[Proved]")
                                                Satisfiable{}   -> (addTag "[Satisfiable]",   addTag "[Failed]")
                                                _               -> let d = diag res in (addTag d, addTag d)

             when chatty $ putStrLn $ topName '<' caseMsg

             return $ wrap res

            where topName c w  = tag c ++ topTag ++ " Parallel case split: " ++ range ++ ": " ++ w

                  topTag = " Case" ++ s ++ intercalate "." lids ++ dot ++ "[1-" ++ show (length cs + 1) ++ "]:"
                    where dot | null lids = ""
                              | True      = "."
                          s   | null cs   = " "
                              | True      = "s "

                  range   = case cs of
                              []  -> "Coverage"
                              [_] -> "One case and coverage"
                              xs  -> show (length xs) ++ " cases and coverage"

        -- Parallel decision:
        --      - If SAT:   Run all cases in parallel and return a SAT result from any. If none-of-them is SAT, then we return the last finishing
        --      - If Prove: Run all cases in parallel and return the last one if all return UNSAT. Otherwise return the first SAT one.
        decideParallel :: [(String, IO SMTResult)] -> IO (String, SMTResult)
        decideParallel caseTasks = mapM try caseTasks >>= pick
          where try (nm, task) = async $ task >>= \r -> return (nm, r)

                pick :: [Async (String, SMTResult)] -> IO (String, SMTResult)
                pick []  = error "SBV.caseSplit.decideParallel: Impossible happened, ran out of proofs!"
                pick [a] = wait a
                pick as  = do (d, r) <- waitAny as
                              let others   = filter (/= d) as
                                  continue = pick others
                                  stop     = mapM_ cancel others >> return r
                              case snd r of
                                Unsatisfiable{} -> continue
                                Satisfiable{}   -> stop
                                SatExtField{}   -> stop
                                ProofError{}    -> stop
                                Unknown{}       -> if isSAT then continue else stop
                                TimeOut{}       -> if isSAT then continue else stop

-- | Check if any of the assertions can be violated
safeWith :: SExecutable a => SMTConfig -> a -> IO [SafeResult]
safeWith cfg a = fst <$> runSymbolic' (SMTMode ISetup True cfg) (sName_ a >> check)
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
                                       TimeOut{}       -> False   -- conservative

-- | Determine if the constraints are vacuous using the given SMT-solver. Also see
-- the 'CheckConstrVacuity' tactic.
isVacuousWith :: Provable a => SMTConfig -> a -> IO Bool
isVacuousWith cfg a = fst <$> runSymbolic' (SMTMode ISetup True cfg) (forSome_ a >> query check)  -- NB. Can't call runWithQuery since last constraint would become the implication!
   where check = do cs <- Control.checkSat
                    case cs of
                      Control.Unsat -> return True
                      Control.Sat   -> return False
                      Control.Unk   -> error "SBV: isVacuous: Solver returned unknown!"

-- | Find all satisfying assignments using the given SMT-solver
allSatWith :: Provable a => SMTConfig -> a -> IO AllSatResult
allSatWith = runWithQuery True $ AllSatResult <$> Control.getAllSatResult

simulate :: Provable a => SMTConfig -> Bool -> [String] -> a -> IO (State, SMTProblem)
simulate config isSat comments predicate = do
        let msg       = when (verbose config) . putStrLn . ("** " ++)
            isTiming  = timing config

        msg "Starting symbolic simulation.."
        (_, st, res) <- timeIf isTiming rnf $ runSymbolicWithState (isSat, config) $ (if isSat then forSome_ else forAll_) predicate >>= output
        msg $ "Generated symbolic trace:\n" ++ show res

        let problem = runProofOn config isSat comments res
        rnf problem `seq` return (st, problem)

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

-- | Run an external proof on the given condition to see if it is satisfiable.
internalSATCheck :: SMTConfig -> SBool -> State -> String -> IO SatResult
internalSATCheck cfg condInPath st msg = do
   sw <- sbvToSW st condInPath
   () <- forceSWArg sw
   Result ki tr uic is cs ts as uis ax asgn cstr tactics options goals assertions _ <- extractSymbolicSimulationState st

   let -- Construct the corresponding sat-checker for the branch. Note that we need to
       -- forget about the quantifiers and just use an "exist", as we're looking for a
       -- point-satisfiability check here; whatever the original program was.
       pgm = Result ki tr uic [(EX, n) | (_, n) <- is] cs ts as uis ax asgn cstr tactics options goals assertions [sw]

       mwrap [r] = SatResult r
       mwrap xs  = error $ "SBV.internalSATCheck: Backend solver returned a non-singleton answer:\n" ++ show (map SatResult xs)

       problem = runProofOn cfg True [] pgm

   callSolver True msg [] mwrap problem cfg st Nothing NoCase

-- | Run a custom query
query :: Query a -> Symbolic a
query (Query userQuery) = do
     st <- ask
     case runMode st of
        SMTMode ISetup isSAT cfg -> liftIO $ do let backend = engine (solver cfg)
                                                    m' = SMTMode IRun isSAT cfg

                                                res <- extractSymbolicSimulationState st

                                                let SMTProblem{smtOptions, smtLibPgm} = runProofOn cfg isSAT [] res
                                                    cfg' = cfg { solverSetOptions = solverSetOptions cfg ++ smtOptions }
                                                    pgm  = smtLibPgm cfg' NoCase

                                                backend cfg' st (show pgm) $ \ctx -> evalStateT userQuery ctx{runMode = m'}
        m -> error $ unlines [ ""
                             , "*** Data.SBV: Invalid query call."
                             , "***"
                             , "***   Current mode: " ++ show m
                             , "***"
                             , "*** Query calls are only valid within runSMT/runSMTWith calls"
                             ]


-- TODO: Needs to go!
callSolver :: a
callSolver = error "Prover.callSolver. Needs to go!"

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
