
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
{-# LANGUAGE BangPatterns         #-}
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
       , optimize, optimizeWith
       , isVacuous, isVacuousWith
       , SatModel(..), Modelable(..), displayModels, extractModels
       , getModelDictionaries, getModelValues, getModelUninterpretedValues
       , boolector, cvc4, yices, z3, mathSAT, abc, defaultSMTCfg
       , compileToSMTLib, generateSMTBenchmarks
       , internalSATCheck
       ) where

import Data.Char         (isSpace)
import Data.List         (intercalate, nub)

import Control.Monad     (when, unless, mplus)
import System.FilePath   (addExtension, splitExtension)
import Data.Time         (getCurrentTime, utcToLocalZonedTime)
import System.IO         (hGetBuffering, hSetBuffering, stdout, hFlush, BufferMode(..))
import System.IO.Unsafe  (unsafeInterleaveIO)

import Control.Concurrent.Async (async, wait, cancel, waitAny, Async)

import GHC.Stack.Compat
#if !MIN_VERSION_base(4,9,0)
import GHC.SrcLoc.Compat
#endif

import qualified Data.Set as Set (toList)

import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic
import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib
import Data.SBV.SMT.Utils
import Data.SBV.Utils.TDiff

import qualified Data.SBV.Control as Control

import Control.DeepSeq (rnf)
import Control.Exception (bracket)

import qualified Data.IORef as IORef (newIORef, readIORef, writeIORef)

import qualified Data.SBV.Provers.Boolector  as Boolector
import qualified Data.SBV.Provers.CVC4       as CVC4
import qualified Data.SBV.Provers.Yices      as Yices
import qualified Data.SBV.Provers.Z3         as Z3
import qualified Data.SBV.Provers.MathSAT    as MathSAT
import qualified Data.SBV.Provers.ABC        as ABC

mkConfig :: SMTSolver -> SMTLibVersion -> [String] -> SMTConfig
mkConfig s smtVersion tweaks = SMTConfig { verbose          = False
                                         , timing           = NoTiming
                                         , sBranchTimeOut   = Nothing
                                         , timeOut          = Nothing
                                         , printBase        = 10
                                         , printRealPrec    = 16
                                         , smtFile          = Nothing
                                         , solver           = s
                                         , solverTweaks     = tweaks
                                         , smtLibVersion    = smtVersion
                                         , optimizeArgs     = []
                                         , satCmd           = "(check-sat)"
                                         , isNonModelVar    = const False  -- i.e., everything is a model-variable by default
                                         , roundingMode     = RoundNearestTiesToEven
                                         , solverSetOptions = []
                                         , customQuery      = Nothing
                                         }

-- | Default configuration for the Boolector SMT solver
boolector :: SMTConfig
boolector = mkConfig Boolector.boolector SMTLib2 []

-- | Default configuration for the CVC4 SMT Solver.
cvc4 :: SMTConfig
cvc4 = mkConfig CVC4.cvc4 SMTLib2 []

-- | Default configuration for the Yices SMT Solver.
yices :: SMTConfig
yices = mkConfig Yices.yices SMTLib2 []

-- | Default configuration for the Z3 SMT solver
z3 :: SMTConfig
z3 = mkConfig Z3.z3 SMTLib2 []

-- | Default configuration for the MathSAT SMT solver
mathSAT :: SMTConfig
mathSAT = mkConfig MathSAT.mathSAT SMTLib2 []

-- | Default configuration for the ABC synthesis and verification tool.
abc :: SMTConfig
abc = mkConfig ABC.abc SMTLib2 []

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

-- | Prove a predicate, equivalent to @'proveWith' 'defaultSMTCfg'@
prove :: Provable a => a -> IO ThmResult
prove = proveWith defaultSMTCfg

-- | Find a satisfying assignment for a predicate, equivalent to @'satWith' 'defaultSMTCfg'@
sat :: Provable a => a -> IO SatResult
sat = satWith defaultSMTCfg

-- | Return all satisfying assignments for a predicate, equivalent to @'allSatWith' 'defaultSMTCfg'@.
-- Satisfying assignments are constructed lazily, so they will be available as returned by the solver
-- and on demand.
--
-- NB. Uninterpreted constant/function values and counter-examples for array values are ignored for
-- the purposes of @'allSat'@. That is, only the satisfying assignments modulo uninterpreted functions and
-- array inputs will be returned. This is due to the limitation of not having a robust means of getting a
-- function counter-example back from the SMT solver.
allSat :: Provable a => a -> IO AllSatResult
allSat = allSatWith defaultSMTCfg

-- | Optimize a given collection of `Objective`s
optimize :: Provable a => a -> IO OptimizeResult
optimize = optimizeWith defaultSMTCfg

-- | Check that all the 'sAssert' calls are safe, equivalent to @'safeWith' 'defaultSMTCfg'@
safe :: SExecutable a => a -> IO [SafeResult]
safe = safeWith defaultSMTCfg

-- | Check if the given constraints are satisfiable, equivalent to @'isVacuousWith' 'defaultSMTCfg'@.
-- See the function 'constrain' for an example use of 'isVacuous'. Also see the 'CheckConstrVacuity'
-- tactic.
isVacuous :: Provable a => a -> IO Bool
isVacuous = isVacuousWith defaultSMTCfg

-- Decision procedures (with optional timeout)

-- | Check whether a given property is a theorem, with an optional time out and the given solver.
-- Returns @Nothing@ if times out, or the result wrapped in a @Just@ otherwise.
isTheoremWith :: Provable a => SMTConfig -> Maybe Int -> a -> IO (Maybe Bool)
isTheoremWith cfg mbTo p = do r <- proveWith cfg{timeOut = mbTo} p
                              case r of
                                ThmResult Unsatisfiable{} -> return $ Just True
                                ThmResult Satisfiable{}   -> return $ Just False
                                ThmResult TimeOut{}       -> return Nothing
                                _                         -> error $ "SBV.isTheorem: Received:\n" ++ show r

-- | Check whether a given property is satisfiable, with an optional time out and the given solver.
-- Returns @Nothing@ if times out, or the result wrapped in a @Just@ otherwise.
isSatisfiableWith :: Provable a => SMTConfig -> Maybe Int -> a -> IO (Maybe Bool)
isSatisfiableWith cfg mbTo p = do r <- satWith cfg{timeOut = mbTo} p
                                  case r of
                                    SatResult Satisfiable{}   -> return $ Just True
                                    SatResult Unsatisfiable{} -> return $ Just False
                                    SatResult TimeOut{}       -> return Nothing
                                    _                         -> error $ "SBV.isSatisfiable: Received: " ++ show r

-- | Checks theoremhood within the given optional time limit of @i@ seconds.
-- Returns @Nothing@ if times out, or the result wrapped in a @Just@ otherwise.
isTheorem :: Provable a => Maybe Int -> a -> IO (Maybe Bool)
isTheorem = isTheoremWith defaultSMTCfg

-- | Checks satisfiability within the given optional time limit of @i@ seconds.
-- Returns @Nothing@ if times out, or the result wrapped in a @Just@ otherwise.
isSatisfiable :: Provable a => Maybe Int -> a -> IO (Maybe Bool)
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
        (_, SMTProblem{smtLibPgm}) <- simulate (toSMTLib cfg) cfg isSat comments a
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

-- | Make sure sat/prove calls don't have objectives, and optimize does!
objectiveCheck :: Bool -> [Objective a] -> String -> IO ()
objectiveCheck False [] _ = return ()
objectiveCheck False os w = error $ unlines $ ("\n*** Unsupported call to " ++ show w ++ " in the presence of objective(s):")
                                            : [ "***\t" ++ intercalate ", " (map objectiveName os)
                                              , "*** Use \"optimize\" to optimize for these objectives instead of " ++ show w
                                              ]
objectiveCheck True []  w = error $ "*** Unsupported call to " ++ w ++ " when no objectives are present. Use \"sat\" for plain satisfaction"
objectiveCheck True _   _ = return ()

-- | Proves the predicate using the given SMT-solver
proveWith :: Provable a => SMTConfig -> a -> IO ThmResult
proveWith config a = do (ctx, simRes@SMTProblem{tactics, smtOptions, objectives}) <- simulate (toSMTLib config) config False [] a
                        objectiveCheck False objectives "prove"
                        let hasPar = any isParallelCaseAnywhere tactics
                        bufferSanity hasPar $ applyTactics config ctx (False, hasPar) (wrap, unwrap) [] smtOptions tactics objectives
                                            $ callSolver False "Checking Theoremhood.." [] mwrap simRes
  where wrap                 = ThmResult
        unwrap (ThmResult r) = r

        mwrap [r] = wrap r
        mwrap xs  = error $ "SBV.proveWith: Backend solver returned a non-singleton answer:\n" ++ show (map ThmResult xs)

-- | Find a satisfying assignment using the given SMT-solver
satWith :: Provable a => SMTConfig -> a -> IO SatResult
satWith config a = do (ctx, simRes@SMTProblem{tactics, smtOptions, objectives}) <- simulate (toSMTLib config) config True [] a
                      objectiveCheck False objectives "sat"
                      let hasPar = any isParallelCaseAnywhere tactics
                      bufferSanity hasPar $ applyTactics config ctx (True, hasPar) (wrap, unwrap) [] smtOptions tactics objectives
                                          $ callSolver True "Checking Satisfiability.." [] mwrap simRes
  where wrap                 = SatResult
        unwrap (SatResult r) = r

        mwrap [r] = wrap r
        mwrap xs  = error $ "SBV.satWith: Backend solver returned a non-singleton answer:\n" ++ show (map SatResult xs)

-- | Optimizes the objectives using the given SMT-solver
optimizeWith :: Provable a => SMTConfig -> a -> IO OptimizeResult
optimizeWith config a = do
        msg "Optimizing.."
        (ctx, sbvPgm@SMTProblem{objectives, tactics}) <- simulate (toSMTLib config) config True [] a

        objectiveCheck True objectives "optimize"

        let hasPar  = any isParallelCaseAnywhere tactics
            style = case nub [s | OptimizePriority s <- tactics] of
                      []  -> Lexicographic
                      [s] -> s
                      ss  -> error $ "SBV: Multiple optimization priorities found: " ++ intercalate ", " (map show ss) ++ ". Please use only one."


            optimizer = case style of
               Lexicographic -> optLexicographic
               Independent   -> optIndependent
               Pareto mbN    -> optPareto mbN

        optimizer hasPar config ctx sbvPgm

  where msg = when (verbose config) . putStrLn . ("** " ++)

-- | Construct a lexicographic optimization result
optLexicographic :: Bool -> SMTConfig -> QueryContext -> SMTProblem -> IO OptimizeResult
optLexicographic hasPar config ctx sbvPgm@SMTProblem{objectives, smtOptions, tactics} = do
        result <- bufferSanity hasPar $ applyTactics config ctx (True, hasPar) (id, id) [] smtOptions tactics objectives
                                      $ callSolver True "Lexicographically optimizing.." [] mwrap sbvPgm
        return $ LexicographicResult result

  where mwrap [r] = r
        mwrap xs  = error $ "SBV.optLexicographic: Backend solver returned a non-singleton answer:\n" ++ show (map SatResult xs)

-- | Construct an independent optimization result
optIndependent :: Bool -> SMTConfig -> QueryContext -> SMTProblem -> IO OptimizeResult
optIndependent hasPar config ctx sbvPgm@SMTProblem{objectives, smtOptions, tactics} = do
        let ns = map objectiveName objectives
        result <- bufferSanity hasPar $ applyTactics config ctx (True, hasPar) (wrap ns, unwrap) [] smtOptions tactics objectives
                                      $ callSolver True "Independently optimizing.." [] mwrap sbvPgm
        return $ IndependentResult result

  where wrap :: [String] -> SMTResult -> [(String, SMTResult)]
        wrap ns r = zip ns (repeat r)

        -- the role of unwrap here is to take the result with more info in case a case-split is
        -- performed and we need to decide in a SAT context.
        unwrap :: [(String, SMTResult)] -> SMTResult
        unwrap xs = case [r | (_, r@Satisfiable{}) <- xs] ++ [r | (_, r@SatExtField{}) <- xs] ++ map snd xs of
                     (r:_) -> r
                     []    -> error "SBV.optIndependent: Impossible happened: Received no results!"

        mwrap xs
         | lobs == lxs = zip (map objectiveName objectives) xs
         | True        = error $ "SBV.optIndependent: Expected " ++ show lobs ++ " objective results, but received: " ++ show lxs ++ ":\n" ++ show (map SatResult xs)
         where lxs  = length xs
               lobs = length objectives

-- | Construct a pareto-front optimization result
optPareto :: Maybe Int -> Bool -> SMTConfig -> QueryContext -> SMTProblem -> IO OptimizeResult
optPareto mbN hasPar config ctx sbvPgm@SMTProblem{objectives, smtOptions, tactics=origTactics} = do

        -- make sure we don't have a query already
        case [() | QueryUsing _ <- origTactics] of
           [] -> return ()
           _  -> error $ unlines [ ""
                                 , "*** Data.SBV: Pareto-front extraction is not supported in the presence of custom queries."
                                 , "*** Data.SBV: Please report this as a feature request!"
                                 ]

        -- The only way to communicate back from the tactic is to use an IORef here! This is
        -- totally safe, though I wish there was a better way to do this.
        isParetoLimitReached <- IORef.newIORef False

        let tactics = QueryUsing paretoTactic : origTactics

            -- Continuously query
            paretoTactic = let loop (Just i) ms
                                 | i <= 0
                                 = do Control.io $ IORef.writeIORef isParetoLimitReached True
                                      return (reverse ms)

                               loop mbi ms = do cs <- Control.checkSat
                                                case cs of
                                                  Control.Sat -> do m <- Control.getModel
                                                                    loop (subtract 1 <$> mbi) (m:ms)
                                                  _           -> return (reverse ms)
                           in loop mbN []

        result <- bufferSanity hasPar $ applyTactics config ctx (True, hasPar) (wrap, unwrap) [] smtOptions tactics objectives
                                      $ callSolver True "Pareto optimizing.." [] id sbvPgm

        limitReached <- IORef.readIORef isParetoLimitReached

        return $ ParetoResult limitReached result

  where wrap :: SMTResult -> [SMTResult]
        wrap r = [r]

        -- the role of unwrap here is to take the result with more info in case a case-split is
        -- performed and we need to decide in a SAT context.
        unwrap :: [SMTResult] -> SMTResult
        unwrap xs = case [r | r@Satisfiable{} <- xs] ++ [r | r@SatExtField{} <- xs] ++ xs of
                     (r:_) -> r
                     []    -> error "SBV.optPareto: Impossible happened: Received no results!"

-- | Apply the given tactics to a problem
applyTactics :: SMTConfig                                                                       -- ^ Solver configuration
             -> QueryContext                                                                    -- ^ Context for user queries
             -> (Bool, Bool)                                                                    -- ^ Are we a sat-problem? Do we have anything parallel going on? (Parallel-case split.)
             -> (SMTResult -> res, res -> SMTResult)                                            -- ^ Wrapper/unwrapper pair from result to SMT answer
             -> [(String, (String, SW))]                                                        -- ^ Level at which we are called. (In case of a nested case-split)
             -> [Control.SMTOption]                                                             -- ^ Options to set
             -> [Tactic SW]                                                                     -- ^ Tactics active at this level
             -> [Objective (SW, SW)]                                                            -- ^ Optimization goals we have
             -> (SMTConfig -> QueryContext -> Maybe (OptimizeStyle, Int) -> CaseCond -> IO res) -- ^ The actual continuation at this point
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

        when hasQueries $ maybe (return ()) error $ checkQueryApplicability cfgIn hasCaseSplits ctx

        let mbOptInfo
                | not hasObjectives = Nothing
                | True              = Just (optimizePriority, length objectives)

        if hasObjectives

           then cont (finalOptConfig objectives) ctx mbOptInfo (Opt objectives)

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

  where (caseSplits, checkCaseVacuity, parallelCases, checkConstrVacuity, timeOuts, checkUsing, useSolvers, optimizePriorities, queryUsings)
                = foldr (flip classifyTactics) ([], [], [], [], [], [], [], [], []) tactics

        classifyTactics (a, b, c, d, e, f, g, h, i) = \case
                    t@CaseSplit{}           -> (t:a,   b,   c,   d,   e,   f,   g,   h,   i)
                    t@CheckCaseVacuity{}    -> (  a, t:b,   c,   d,   e,   f,   g,   h,   i)
                    t@ParallelCase{}        -> (  a,   b, t:c,   d,   e,   f,   g,   h,   i)
                    t@CheckConstrVacuity{}  -> (  a,   b,   c, t:d,   e,   f,   g,   h,   i)
                    t@StopAfter{}           -> (  a,   b,   c,   d, t:e,   f,   g,   h,   i)
                    t@CheckUsing{}          -> (  a,   b,   c,   d,   e, t:f,   g,   h,   i)
                    t@UseSolver{}           -> (  a,   b,   c,   d,   e,   f, t:g,   h,   i)
                    t@OptimizePriority{}    -> (  a,   b,   c,   d,   e,   f,   g, t:h,   i)
                    t@QueryUsing{}          -> (  a,   b,   c,   d,   e,   f,   g,   h, t:i)

        hasObjectives = not $ null objectives

        hasCaseSplits = not $ null cases

        hasQueries    = not $ null queryUsings

        parallelCase  = not $ null parallelCases

        optimizePriority = case [s | OptimizePriority s <- optimizePriorities] of
                             []  -> Lexicographic
                             [s] -> s
                             ss  -> error $ "SBV.OptimizePriority: Multiple optimization priorities found, at most one is allowed: " ++ intercalate "," (map show ss)

        shouldCheckCaseVacuity = case [b | CheckCaseVacuity b <- checkCaseVacuity] of
                                   [] -> True   -- default is to check-case-vacuity
                                   bs -> or bs  -- otherwise check vacuity if we're asked to do so

        -- for constraint vacuity, default is *not* to check; so a simple or suffices
        shouldCheckConstrVacuity = or [b | CheckConstrVacuity b <- checkConstrVacuity]

        (chatty, cases) = let (vs, css) = unzip [(v, cs) | CaseSplit v cs <- caseSplits] in (or (verbose cfgIn : vs), concat css)

        grabStops c = case [i | StopAfter i <- timeOuts] of
                        [] -> c
                        xs -> c {timeOut = Just (maximum xs)}

        grabCheckUsing c = case [s | CheckUsing s <- checkUsing] of
                             []  -> c
                             [s] -> c {satCmd = "(check-sat-using " ++ s ++ ")"}
                             ss  -> c {satCmd = "(check-sat-using (then " ++ unwords ss ++ "))"}

        grabQueryUsing c = case [f | QueryUsing f <- queryUsings] of
                              []  -> c
                              [f] -> c { customQuery = Just f }
                              _   -> error "SBV.QueryUsing: Multiple user-continuations found, at most one is allowed."

        configToUse = case [s | UseSolver s <- useSolvers] of
                        []  -> cfgIn
                        [s] -> s
                        ss  -> error $ "SBV.UseSolver: Multiple UseSolver tactics found, at most one is allowed: " ++ intercalate "," (map show ss)

        grabSetOptions c = c { solverSetOptions = smtOptions ++ solverSetOptions c }

        finalConfig = grabQueryUsing . grabSetOptions . grabCheckUsing . grabStops $ configToUse

        finalOptConfig goals = finalConfig { optimizeArgs  = optimizeArgs finalConfig ++ optimizerDirectives }
            where optimizerDirectives
                        | hasObjectives = map minmax goals ++ style optimizePriority
                        | True          = []

                  minmax (Minimize   _  (_, v))     = "(minimize "    ++ show v ++ ")"
                  minmax (Maximize   _  (_, v))     = "(maximize "    ++ show v ++ ")"
                  minmax (AssertSoft nm (_, v) mbp) = "(assert-soft " ++ show v ++ penalize mbp ++ ")"
                    where penalize DefaultPenalty    = ""
                          penalize (Penalty w mbGrp)
                             | w <= 0         = error $ unlines [ "SBV.AssertSoft: Goal " ++ show nm ++ " is assigned a non-positive penalty: " ++ shw
                                                                , "All soft goals must have > 0 penalties associated."
                                                                ]
                             | True           = " :weight " ++ shw ++ maybe "" group mbGrp
                             where shw = show (fromRational w :: Double)
                          group g = " :id " ++ g

                  style Lexicographic = [] -- default, no option needed
                  style Independent   = ["(set-option :opt.priority box)"]
                  style (Pareto _)    = ["(set-option :opt.priority pareto)"]

-- | Should we allow a custom query? Returns the reason why we shouldn't, if there is one
checkQueryApplicability :: SMTConfig -> Bool -> QueryContext -> Maybe String
checkQueryApplicability cfgIn hasCaseSplits QueryContext{contextSkolems} =
                checkSupport    (supportsCustomQueries $ capabilities $ solver cfgIn)
        `mplus` checkSkolems    contextSkolems
        `mplus` checkCaseSplits hasCaseSplits
  where
        -- Check if the underlying solver has support for it
        checkSupport True  = Nothing
        checkSupport False = noInteractive [ "Chosen solver does not support interactive queries:"
                                           , "   Solver: " ++ show (solver cfgIn)
                                           ]

        -- Can't execute queries if there are quantified skolem vars, as those generate
        -- quantified formulae and thus variables won't be visible to the user past the query
        checkSkolems [] = Nothing
        checkSkolems xs = noInteractive [ "Queries in the presence of quantified variable(s):"
                                        , "  " ++   intercalate ", " (map show xs)
                                        ]
        -- Can execute queries if there are case splits. This is an interesting (but probablt inconsequential) restriction. The
        -- reason why is that case-splits rely on the fact that the internal state of SBV remains constant once we are done
        -- simulating. But the whole point of a query is to alter that state further! Thus, if we run a query in a case-split
        -- context, we'd have a terrible race condition. If absolutely necessary, this can be worked around by making a "deep copy"
        -- of the state and all it's IORefs as we go down a branch, but that can be costly and could lead to space leaks. Let's
        -- fight that battle if it actually does become an issue.
        checkCaseSplits False = Nothing
        checkCaseSplits True  = noInteractive [ "Queries in the presence of case splits."]

        noInteractive :: [String] -> Maybe String
        noInteractive ss = Just $ unlines $  "*** Data.SBV: Unsupported interactive/query mode feature."
                                          :  map ("***  " ++) ss
                                          ++ ["*** Data.SBV: Please report this as a feature request!"]

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
                          Bool                                                                            -- ^ isSAT?
                       -> SMTConfig                                                                       -- ^ config
                       -> QueryContext                                                                    -- ^ query context
                       -> Maybe (OptimizeStyle, Int)                                                      -- ^ optimization info
                       -> (SMTResult -> res, res -> SMTResult)                                            -- ^ wrappers back and forth from final result
                       -> (SMTConfig -> QueryContext -> Maybe (OptimizeStyle, Int) -> CaseCond -> IO res) -- ^ continuation
                       -> IO (Maybe res)                                                                  -- ^ result, wrapped in Maybe if vacuity fails
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
             SMTConfig                                                                       -- ^ Solver config
          -> QueryContext                                                                    -- ^ Context for queries
          -> Maybe (OptimizeStyle, Int)                                                      -- ^ Are we optimizing?
          -> Bool                                                                            -- ^ Should we check vacuity of cases?
          -> (Bool, Bool)                                                                    -- ^ Should we run the cases in parallel? Second bool: Is anything parallel going on?
          -> Bool                                                                            -- ^ True if we're sat solving
          -> (SMTResult -> res, res -> SMTResult)                                            -- ^ wrapper, unwrapper from sat/proof to the actual result
          -> [(String, (String, SW))]                                                        -- ^ Path condition as we reached here. (In a nested case split, First #, then actual name.)
          -> [Control.SMTOption]                                                             -- ^ Options to pass down
          -> Bool                                                                            -- ^ Should we be chatty on the case-splits?
          -> [(String, SW, [Tactic SW])]                                                     -- ^ List of cases. Case name, condition, plus further tactics for nested case-splitting etc.
          -> (SMTConfig -> QueryContext -> Maybe (OptimizeStyle, Int) -> CaseCond -> IO res) -- ^ The "solver" once we provide it with a problem and a case
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
safeWith cfg a = do
        (st, res@Result{resAssertions=asserts}) <- runSymbolicWithState (True, cfg) $ sName_ a >>= output
        mapM (verify st res) asserts
  where locInfo (Just ps) = Just $ let loc (f, sl) = concat [srcLocFile sl, ":", show (srcLocStartLine sl), ":", show (srcLocStartCol sl), ":", f]
                                   in intercalate ",\n " (map loc ps)
        locInfo _                     = Nothing
        verify st res (msg, cs, cond) = do (ctx, problem) <- runProofOn (toSMTLib cfg) cfg True [] st pgm
                                           result         <- callSolver True msg [] mwrap problem cfg ctx Nothing NoCase
                                           return $ SafeResult (locInfo (getCallStack `fmap` cs), msg, result)
           where pgm = res { resInputs  = [(EX, n) | (_, n) <- resInputs res]   -- make everything existential
                           , resOutputs = [cond]
                           }
                 mwrap [r] = r
                 mwrap xs  = error $ "SBV.safeWith: Backend solver returned a non-singleton answer:\n" ++ show (map SatResult xs)

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
isVacuousWith config a = do
        (st, Result ki tr uic is cs ts as uis ax asgn cstr tactics options goals asserts _out) <- runSymbolicWithState (True, config) $ forAll_ a >>= output
        case cstr of
           [] -> return False -- no constraints, no need to check
           _  -> do let is'  = [(EX, i) | (_, i) <- is] -- map all quantifiers to "exists" for the constraint check
                        res' = Result ki tr uic is' cs ts as uis ax asgn cstr tactics options goals asserts [trueSW]
                    (ctx, problem) <- runProofOn (toSMTLib config) config True [] st res'
                    result         <- callSolver True "Checking Vacuity.." [] mwrap problem config ctx Nothing NoCase
                    case result of
                      Unsatisfiable{} -> return True  -- constraints are unsatisfiable!
                      Satisfiable{}   -> return False -- constraints are satisfiable!
                      SatExtField{}   -> error "SBV: isVacuous: Solver returned a model in the extension field!"
                      Unknown{}       -> error "SBV: isVacuous: Solver returned unknown!"
                      ProofError _ ls -> error $ "SBV: isVacuous: error encountered:\n" ++ unlines ls
                      TimeOut _       -> error "SBV: isVacuous: time-out."
        where mwrap [r] = r
              mwrap xs  = error $ "SBV.isVacuousWith: Backend solver returned a non-singleton answer:\n" ++ show (map SatResult xs)

-- | Find all satisfying assignments using the given SMT-solver
allSatWith :: Provable a => SMTConfig -> a -> IO AllSatResult
allSatWith config p = do
        msg "Checking Satisfiability, all solutions.."
        (ctx, sbvPgm@SMTProblem{smtInputs=qinps, kindsUsed=ki}) <- simulate (toSMTLib config) config True [] p

        let usorts = [s | us@(KUserSort s _) <- Set.toList ki, isFree us]
                where isFree (KUserSort _ (Left _)) = True
                      isFree _                      = False

        unless (null usorts) $ msg $  "SBV.allSat: Uninterpreted sorts present: " ++ unwords usorts
                                   ++ "\n               SBV will use equivalence classes to generate all-satisfying instances."

        -- We cannot support allSat with custom-queries, since the state would be reused!

        unless (null [() | QueryUsing _ <- tactics sbvPgm])
               $ error $ unlines [ "*** Data.SBV: allSat calls are not supported in the presence of interactive queries."
                                 , "*** Data.SBV: Please report this as a feature request!"
                                 ]

        results <- unsafeInterleaveIO $ go ctx sbvPgm (1::Int) []

        -- See if there are any existentials below any universals
        -- If such is the case, then the solutions are unique upto prefix existentials
        let w = ALL `elem` map fst qinps
        return $ AllSatResult (w,  results)
  where msg = when (verbose config) . putStrLn . ("** " ++)
        go ctx sbvPgm = loop
          where hasPar = any isParallelCaseAnywhere (tactics sbvPgm)
                loop !n nonEqConsts = do
                  curResult <- invoke nonEqConsts hasPar n ctx sbvPgm
                  case curResult of
                    Nothing            -> return []
                    Just (SatResult r) -> let cont model = do let modelOnlyAssocs = [v | v@(x, _) <- modelAssocs model, not (isNonModelVar config x)]
                                                              rest <- unsafeInterleaveIO $ loop (n+1) (modelOnlyAssocs : nonEqConsts)
                                                              return (r : rest)
                                          in case r of
                                               -- We are done! This is really how we should always stop.
                                               Unsatisfiable{} -> return []

                                               -- We have a model. If there are bindings, continue; otherwise stop
                                               Satisfiable   _ (SMTModel _ []) -> return [r]
                                               Satisfiable   _ model           -> cont model

                                               -- Satisfied in an extension field. Stop if no new bindings, otherwise continue if all regular.
                                               -- If the model is in the extension, we also stop
                                               SatExtField   _ (SMTModel _ [])       -> return [r]
                                               SatExtField   _ model@(SMTModel [] _) -> cont model
                                               SatExtField{}                         -> return []

                                               -- Something bad happened, we stop here. Note that we treat Unknown as bad too in this context.
                                               Unknown{}    -> return [r]
                                               ProofError{} -> return [r]
                                               TimeOut{}    -> return [r]

        invoke nonEqConsts hasPar n ctx simRes@SMTProblem{smtInputs, smtOptions, tactics, objectives} = do
               objectiveCheck False objectives "allSat"
               msg $ "Looking for solution " ++ show n
               case addNonEqConstraints (smtLibVersion config) (roundingMode config) smtInputs nonEqConsts of
                 Nothing -> -- no new constraints refuted models, stop
                            return Nothing
                 Just refutedModels -> do

                    let wrap                 = SatResult
                        unwrap (SatResult r) = r

                        mwrap  [r]           = wrap r
                        mwrap xs             = error $ "SBV.allSatWith: Backend solver returned a non-singleton answer:\n" ++ show (map SatResult xs)

                    res <- bufferSanity hasPar $ applyTactics (updateName (n-1) config) ctx (True, hasPar) (wrap, unwrap) [] smtOptions tactics objectives
                                               $ callSolver True "Checking Satisfiability.." refutedModels mwrap simRes
                    return $ Just res

        updateName i cfg = cfg{smtFile = upd `fmap` smtFile cfg}
               where upd nm = let (b, e) = splitExtension nm in b ++ "_allSat_" ++ show i ++ e

callSolver :: Bool -> String -> [String] -> ([SMTResult] -> b) -> SMTProblem -> SMTConfig -> QueryContext -> Maybe (OptimizeStyle, Int) -> CaseCond -> IO b
callSolver isSat checkMsg refutedModels wrap SMTProblem{smtInputs, smtSkolemMap, smtLibPgm} config ctx mbOptInfo caseCond = do
       let msg = when (verbose config) . putStrLn . ("** " ++)
           finalPgm = intercalate "\n" (pgm ++ refutedModels) where SMTLibPgm _ pgm = smtLibPgm config caseCond

       msg checkMsg
       msg $  intercalate "\n" $  "Generated SMTLib program:"
                               : solverTweaks config
                              ++ [finalPgm]
                              ++ optimizeArgs config
                              ++ [satCmd config]

       smtAnswer <- engine (solver config) config ctx isSat mbOptInfo smtInputs smtSkolemMap finalPgm

       msg "Done.."

       return $ wrap smtAnswer

simulate :: Provable a => SMTLibConverter SMTLibPgm -> SMTConfig -> Bool -> [String] -> a -> IO (QueryContext, SMTProblem)
simulate converter config isSat comments predicate = do
        let msg = when (verbose config) . putStrLn . ("** " ++)
            isTiming = timing config
        msg "Starting symbolic simulation.."
        (st, res) <- timeIf isTiming ProblemConstruction $ runSymbolicWithState (isSat, config) $ (if isSat then forSome_ else forAll_) predicate >>= output
        msg $ "Generated symbolic trace:\n" ++ show res
        msg "Translating to SMT-Lib.."
        runProofOn converter config isSat comments st res

runProofOn :: SMTLibConverter SMTLibPgm -> SMTConfig -> Bool -> [String] -> State -> Result -> IO (QueryContext, SMTProblem)
runProofOn converter config isSat comments st res =
        let isTiming = timing config
        in case res of
             Result ki _qcInfo _codeSegs is consts tbls arrs uis axs pgm cstrs tacs options goals assertions [o@(SW KBool _)] ->
               timeIf isTiming Translation
                $ let flipQ (ALL, x) = (EX,  x)
                      flipQ (EX,  x) = (ALL, x)

                      skolemize :: [(Quantifier, NamedSymVar)] -> [Either SW (SW, [SW])]
                      skolemize quants = go quants ([], [])
                        where go []                   (_,  sofar) = reverse sofar
                              go ((ALL, (v, _)):rest) (us, sofar) = go rest (v:us, Left v : sofar)
                              go ((EX,  (v, _)):rest) (us, sofar) = go rest (us,   Right (v, reverse us) : sofar)

                      qinps      = if isSat then is else map flipQ is
                      skolemMap  = skolemize qinps
                      skolemVars = [s | (ALL, (_, s)) <- qinps]

                      smtScript = converter ki isSat comments is skolemMap consts tbls arrs uis axs pgm cstrs o
                      problem   = SMTProblem { smtInputs=is, smtSkolemMap=skolemMap, kindsUsed=ki
                                             , smtAsserts=assertions, tactics=tacs, smtOptions=options, objectives=goals, smtLibPgm=smtScript}
                      context   = QueryContext {contextState = st, contextSkolems = skolemVars}

                  in rnf smtScript `seq` return (context, problem)
             Result{resOutputs = os} -> case length os of
                           0  -> error $ "Impossible happened, unexpected non-outputting result\n" ++ show res
                           1  -> error $ "Impossible happened, non-boolean output in " ++ show os
                                       ++ "\nDetected while generating the trace:\n" ++ show res
                           _  -> error $ "User error: Multiple output values detected: " ++ show os
                                       ++ "\nDetected while generating the trace:\n" ++ show res
                                       ++ "\n*** Check calls to \"output\", they are typically not needed!"

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

   (ctx, problem) <- runProofOn (toSMTLib cfg) cfg True [] st pgm
   callSolver True msg [] mwrap problem cfg ctx Nothing NoCase
{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
