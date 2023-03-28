-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Dynamic
-- Copyright : (c) Brian Huffman
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Dynamically typed low-level API to the SBV library, for users who
-- want to generate symbolic values at run-time. Note that with this
-- API it is possible to create terms that are not type correct; use
-- at your own risk!
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Dynamic
  (
  -- * Programming with symbolic values
  -- ** Symbolic types
  -- *** Abstract symbolic value type
    SVal
  , HasKind(..), Kind(..), CV(..), CVal(..), cvToBool
  -- *** SMT Arrays of symbolic values
  , SArr, readSArr, writeSArr, mergeSArr, newSArr, eqSArr
  -- ** Creating a symbolic variable
  , Symbolic
  , Quantifier(..)
  , svMkSymVar, svNewVar_, svNewVar
  , sWordN, sWordN_, sIntN, sIntN_
  -- ** Operations on symbolic values
  -- *** Boolean literals
  , svTrue, svFalse, svBool, svAsBool
  -- *** Integer literals
  , svInteger, svAsInteger
  -- *** Float literals
  , svFloat, svDouble, svFloatingPoint
  -- *** Algebraic reals (only from rationals)
  , svReal, svNumerator, svDenominator
  -- *** Symbolic equality
  , svEqual, svNotEqual, svStrongEqual
  -- *** Constructing concrete lists
  , svEnumFromThenTo
  -- *** Symbolic ordering
  , svLessThan, svGreaterThan, svLessEq, svGreaterEq, svStructuralLessThan
  -- *** Arithmetic operations
  , svPlus, svTimes, svMinus, svUNeg, svAbs
  , svDivide, svQuot, svRem, svQuotRem, svExp
  , svAddConstant, svIncrement, svDecrement
  -- *** Logical operations
  , svAnd, svOr, svXOr, svNot
  , svShl, svShr, svRol, svRor
  -- *** Splitting, joining, and extending
  , svExtract, svJoin, svZeroExtend, svSignExtend
  -- *** Sign-casting
  , svSign, svUnsign
  -- *** Numeric conversions
  , svFromIntegral
  -- *** Indexed lookups
  , svSelect
  -- *** Word-level operations
  , svToWord1, svFromWord1, svTestBit, svSetBit
  , svShiftLeft, svShiftRight
  , svRotateLeft, svRotateRight
  , svBarrelRotateLeft, svBarrelRotateRight
  , svWordFromBE, svWordFromLE
  , svBlastLE, svBlastBE
  -- ** Conditionals: Mergeable values
  , svIte, svLazyIte, svSymbolicMerge
  -- * Uninterpreted sorts, constants, and functions
  , svUninterpreted
  -- * Properties, proofs, and satisfiability
  -- ** Proving properties
  , proveWith
  -- ** Checking satisfiability
  , satWith, allSatWith
  -- ** Checking safety
  , safeWith
  -- * Proving properties using multiple solvers
  , proveWithAll, proveWithAny, satWithAll, satWithAny
  -- * Proving properties using multiple threads
  , proveConcurrentWithAll, proveConcurrentWithAny
  , satConcurrentWithAny, satConcurrentWithAll
  -- * Quick-check
  , svQuickCheck

  -- * Model extraction

  -- ** Inspecting proof results
  , ThmResult(..), SatResult(..), AllSatResult(..), SafeResult(..), OptimizeResult(..), SMTResult(..)

  -- ** Programmable model extraction
  , genParse, getModelAssignment, getModelDictionary
  -- * SMT Interface: Configurations and solvers
  , SMTConfig(..), SMTLibVersion(..), Solver(..), SMTSolver(..), boolector, bitwuzla, cvc4, cvc5, dReal, yices, z3, mathSAT, abc, defaultSolverConfig, defaultSMTCfg, sbvCheckSolverInstallation, getAvailableSolvers

  -- * Symbolic computations
  , outputSVal

  -- * Code generation from symbolic programs
  , SBVCodeGen

  -- ** Setting code-generation options
  , cgPerformRTCs, cgSetDriverValues, cgGenerateDriver, cgGenerateMakefile

  -- ** Designating inputs
  , svCgInput, svCgInputArr

  -- ** Designating outputs
  , svCgOutput, svCgOutputArr

  -- ** Designating return values
  , svCgReturn, svCgReturnArr

  -- ** Code generation with uninterpreted functions
  , cgAddPrototype, cgAddDecl, cgAddLDFlags, cgIgnoreSAssert

  -- ** Code generation with 'Data.SBV.SInteger' and 'Data.SBV.SReal' types
  , cgIntegerSize, cgSRealType, CgSRealType(..)

  -- ** Compilation to C
  , compileToC, compileToCLib

  -- ** Compilation to SMTLib
  , generateSMTBenchmarkSat, generateSMTBenchmarkProof
  ) where

import Control.Monad.Trans (liftIO)

import Data.Map.Strict (Map)

import Data.SBV.Core.Kind
import Data.SBV.Core.Concrete
import Data.SBV.Core.Symbolic
import Data.SBV.Core.Operations

import Data.SBV.Compilers.CodeGen ( SBVCodeGen
                                  , svCgInput, svCgInputArr
                                  , svCgOutput, svCgOutputArr
                                  , svCgReturn, svCgReturnArr
                                  , cgPerformRTCs, cgSetDriverValues, cgGenerateDriver, cgGenerateMakefile
                                  , cgAddPrototype, cgAddDecl, cgAddLDFlags, cgIgnoreSAssert
                                  , cgIntegerSize, cgSRealType, CgSRealType(..)
                                  )
import Data.SBV.Compilers.C       (compileToC, compileToCLib)

import Data.SBV.Provers.Prover (boolector, bitwuzla, cvc4, cvc5, dReal, yices, z3, mathSAT, abc, defaultSMTCfg)
import Data.SBV.SMT.SMT        (ThmResult(..), SatResult(..), SafeResult(..), OptimizeResult(..), AllSatResult(..), genParse)
import Data.SBV                (sbvCheckSolverInstallation, defaultSolverConfig, getAvailableSolvers)

import qualified Data.SBV                as SBV (SBool, proveWithAll, proveWithAny, satWithAll, satWithAny
                                                , proveConcurrentWithAll, proveConcurrentWithAny
                                                , satConcurrentWithAny, satConcurrentWithAll
                                                )
import qualified Data.SBV.Core.Data      as SBV (SBV(..))
import qualified Data.SBV.Core.Model     as SBV (sbvQuickCheck)
import qualified Data.SBV.Provers.Prover as SBV (proveWith, satWith, safeWith, allSatWith, generateSMTBenchmarkSat, generateSMTBenchmarkProof)
import qualified Data.SBV.SMT.SMT        as SBV (Modelable(getModelAssignment, getModelDictionary))

import Data.Time (NominalDiffTime)

-- | Dynamic variant of quick-check
svQuickCheck :: Symbolic SVal -> IO Bool
svQuickCheck = SBV.sbvQuickCheck . fmap toSBool

toSBool :: SVal -> SBV.SBool
toSBool = SBV.SBV

-- | Create SMT-Lib benchmark for a sat call
generateSMTBenchmarkSat :: Symbolic SVal -> IO String
generateSMTBenchmarkSat s = SBV.generateSMTBenchmarkSat (fmap toSBool s)

-- | Create SMT-Lib benchmark for a proof call
generateSMTBenchmarkProof :: Symbolic SVal -> IO String
generateSMTBenchmarkProof s = SBV.generateSMTBenchmarkProof (fmap toSBool s)

-- | Proves the predicate using the given SMT-solver
proveWith :: SMTConfig -> Symbolic SVal -> IO ThmResult
proveWith cfg s = SBV.proveWith cfg (fmap toSBool s)

-- | Find a satisfying assignment using the given SMT-solver
satWith :: SMTConfig -> Symbolic SVal -> IO SatResult
satWith cfg s = SBV.satWith cfg (fmap toSBool s)

-- | Check safety using the given SMT-solver
safeWith :: SMTConfig -> Symbolic SVal -> IO [SafeResult]
safeWith cfg s = SBV.safeWith cfg (fmap toSBool s)

-- | Find all satisfying assignments using the given SMT-solver
allSatWith :: SMTConfig -> Symbolic SVal -> IO AllSatResult
allSatWith cfg s = SBV.allSatWith cfg (fmap toSBool s)

-- | Prove a property with multiple solvers, running them in separate threads. The
-- results will be returned in the order produced.
proveWithAll :: [SMTConfig] -> Symbolic SVal -> IO [(Solver, NominalDiffTime, ThmResult)]
proveWithAll cfgs s = SBV.proveWithAll cfgs (fmap toSBool s)

-- | Prove a property with multiple solvers, running them in separate
-- threads. Only the result of the first one to finish will be
-- returned, remaining threads will be killed.
proveWithAny :: [SMTConfig] -> Symbolic SVal -> IO (Solver, NominalDiffTime, ThmResult)
proveWithAny cfgs s = SBV.proveWithAny cfgs (fmap toSBool s)

-- | Prove a property with query mode using multiple threads. Each query
-- computation will spawn a thread and a unique instance of your solver to run
-- asynchronously. The 'Symbolic' 'SVal' is duplicated for each thread. This
-- function will block until all child threads return.
proveConcurrentWithAll :: SMTConfig -> Symbolic SVal -> [Query SVal] -> IO [(Solver, NominalDiffTime, ThmResult)]
proveConcurrentWithAll cfg s queries = SBV.proveConcurrentWithAll cfg queries (fmap toSBool s)

-- | Prove a property with query mode using multiple threads. Each query
-- computation will spawn a thread and a unique instance of your solver to run
-- asynchronously. The 'Symbolic' 'SVal' is duplicated for each thread. This
-- function will return the first query computation that completes, killing the others.
proveConcurrentWithAny :: SMTConfig -> Symbolic SVal -> [Query SVal] -> IO (Solver, NominalDiffTime, ThmResult)
proveConcurrentWithAny cfg s queries = SBV.proveConcurrentWithAny cfg queries (fmap toSBool s)

-- | Find a satisfying assignment to a property with multiple solvers,
-- running them in separate threads. The results will be returned in
-- the order produced.
satWithAll :: [SMTConfig] -> Symbolic SVal -> IO [(Solver, NominalDiffTime, SatResult)]
satWithAll cfgs s = SBV.satWithAll cfgs (fmap toSBool s)

-- | Find a satisfying assignment to a property with multiple solvers,
-- running them in separate threads. Only the result of the first one
-- to finish will be returned, remaining threads will be killed.
satWithAny :: [SMTConfig] -> Symbolic SVal -> IO (Solver, NominalDiffTime, SatResult)
satWithAny cfgs s = SBV.satWithAny cfgs (fmap toSBool s)

-- | Find a satisfying assignment to a property with multiple threads in query
-- mode. The 'Symbolic' 'SVal' represents what is known to all child query threads.
-- Each query thread will spawn a unique instance of the solver. Only the first
-- one to finish will be returned and the other threads will be killed.
satConcurrentWithAny :: SMTConfig -> [Query b] -> Symbolic SVal -> IO (Solver, NominalDiffTime, SatResult)
satConcurrentWithAny cfg qs s = SBV.satConcurrentWithAny cfg qs (fmap toSBool s)

-- | Find a satisfying assignment to a property with multiple threads in query
-- mode. The 'Symbolic' 'SVal' represents what is known to all child query threads.
-- Each query thread will spawn a unique instance of the solver. This function
-- will block until all child threads have completed.
satConcurrentWithAll :: SMTConfig -> [Query b] -> Symbolic SVal -> IO [(Solver, NominalDiffTime, SatResult)]
satConcurrentWithAll cfg qs s = SBV.satConcurrentWithAll cfg qs (fmap toSBool s)

-- | Extract a model, the result is a tuple where the first argument (if True)
-- indicates whether the model was "probable". (i.e., if the solver returned unknown.)
getModelAssignment :: SMTResult -> Either String (Bool, [CV])
getModelAssignment = SBV.getModelAssignment

-- | Extract a model dictionary. Extract a dictionary mapping the variables to
-- their respective values as returned by the SMT solver. Also see `Data.SBV.SMT.getModelDictionaries`.
getModelDictionary :: SMTResult -> Map String CV
getModelDictionary = SBV.getModelDictionary

-- | Create a named fresh existential variable in the current context
svNewVar :: MonadSymbolic m => Kind -> String -> m SVal
svNewVar k n = symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar (Just EX)) k (Just n)

-- | Create an unnamed fresh existential variable in the current context
svNewVar_ :: MonadSymbolic m => Kind -> m SVal
svNewVar_ k = symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar (Just EX)) k Nothing
