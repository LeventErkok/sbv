---------------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Dynamic
-- Copyright   :  (c) Brian Huffman
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Dynamically typed low-level API to the SBV library, for users who
-- want to generate symbolic values at run-time. Note that with this
-- API it is possible to create terms that are not type correct; use
-- at your own risk!
---------------------------------------------------------------------------------

module Data.SBV.Dynamic
  (
  -- * Programming with symbolic values
  -- ** Symbolic types
  -- *** Abstract symbolic value type
    SVal
  , Kind(..), CW(..), CWVal(..), cwToBool
  , svKind, svBitSize, svSigned
  -- *** Arrays of symbolic values
  , SArr
  , readSArr, resetSArr, writeSArr, mergeSArr, newSArr, eqSArr

  -- ** Creating a symbolic variable
  , Symbolic
  , Quantifier(..)
  , svMkSymVar
  -- ** Operations on symbolic values
  -- *** Boolean literals
  , svTrue, svFalse, svBool, svAsBool
  -- *** Integer literals
  , svInteger, svAsInteger
  -- *** Symbolic equality
  , svEqual, svNotEqual
  -- *** Symbolic ordering
  , svLessThan, svGreaterThan, svLessEq, svGreaterEq
  -- *** Arithmetic operations
  , svPlus, svTimes, svMinus, svUNeg, svAbs
  , svDivide, svQuot, svRem
  -- *** Logical operations
  , svAnd, svOr, svXOr, svNot
  , svShl, svShr, svRol, svRor
  -- *** Splitting, joining, and extending
  , svExtract, svJoin
  -- *** Sign-casting
  , svSign, svUnsign
  -- *** Indexed lookups
  , svSelect
  -- *** Word-level operations
  , svToWord1, svFromWord1, svTestBit
  , svShiftLeft, svShiftRight
  , svRotateLeft, svRotateRight
  -- ** Conditionals: Mergeable values
  , svIte, svLazyIte, svSymbolicMerge
  , svReduceInPathCondition
  -- * Uninterpreted sorts, constants, and functions
  , svUninterpreted
  -- * Properties, proofs, and satisfiability
  -- ** Proving properties
  , proveWith
  -- ** Checking satisfiability
  , satWith
  -- * Proving properties using multiple solvers
  , proveWithAll, proveWithAny, satWithAll, satWithAny, allSatWithAll, allSatWithAny
  -- * Model extraction

  -- ** Inspecting proof results
  , ThmResult(..), SatResult(..), AllSatResult(..), SMTResult(..), SafeResult(..)

  -- ** Programmable model extraction
  , genParse, getModel, getModelDictionary
  -- * SMT Interface: Configurations and solvers
  , SMTConfig(..), SMTLibLogic(..), Logic(..), OptimizeOpts(..), Solver(..), SMTSolver(..), boolector, cvc4, yices, z3, mathSAT, abc, defaultSolverConfig, sbvCurrentSolver, defaultSMTCfg, sbvCheckSolverInstallation, sbvAvailableSolvers

  -- * Symbolic computations
  , outputSVal{-, SymWord(..)-}

  -- * Getting SMT-Lib output (for offline analysis)
  , compileToSMTLib, generateSMTBenchmarks
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
  , cgAddPrototype, cgAddDecl, cgAddLDFlags

  -- ** Code generation with 'SInteger' and 'SReal' types
  , cgIntegerSize, cgSRealType, CgSRealType(..)

  -- ** Compilation to C
  , compileToC, compileToCLib
  ) where

import Data.Map (Map)

import Data.SBV.BitVectors.Kind
import Data.SBV.BitVectors.Concrete
import Data.SBV.BitVectors.Symbolic
import Data.SBV.BitVectors.Operations

import Data.SBV.Compilers.CodeGen
  ( SBVCodeGen
  , svCgInput, svCgInputArr
  , svCgOutput, svCgOutputArr
  , svCgReturn, svCgReturnArr
  , cgPerformRTCs, cgSetDriverValues, cgGenerateDriver, cgGenerateMakefile
  , cgAddPrototype, cgAddDecl, cgAddLDFlags
  , cgIntegerSize, cgSRealType, CgSRealType(..)
  )
import Data.SBV.Compilers.C
  ( compileToC, compileToCLib )
import Data.SBV.Provers.Prover
  ( boolector, cvc4, yices, z3, mathSAT, abc, defaultSMTCfg )
import Data.SBV.SMT.SMT
  ( ThmResult(..), SatResult(..), AllSatResult(..), SafeResult(..), genParse )
import Data.SBV.Tools.Optimize
  ( OptimizeOpts(..) )
import Data.SBV
  ( sbvCurrentSolver, sbvCheckSolverInstallation, defaultSolverConfig, sbvAvailableSolvers )

import qualified Data.SBV as SBV
  ( SBool, proveWithAll, proveWithAny, satWithAll, satWithAny, allSatWithAll, allSatWithAny )
import qualified Data.SBV.BitVectors.Data as SBV
  ( SBV(..) )
import qualified Data.SBV.BitVectors.Model as SBV
  ( reduceInPathCondition )
import qualified Data.SBV.Provers.Prover as SBV
  ( proveWith, satWith, compileToSMTLib, generateSMTBenchmarks )
import qualified Data.SBV.SMT.SMT as SBV
  ( Modelable(getModel, getModelDictionary) )

-- | Reduce a condition (i.e., try to concretize it) under the given path
svReduceInPathCondition :: SVal -> SVal
svReduceInPathCondition t = c
  where SBV.SBV c = SBV.reduceInPathCondition (SBV.SBV t)

toSBool :: SVal -> SBV.SBool
toSBool = SBV.SBV

-- | Compiles to SMT-Lib and returns the resulting program as a string. Useful for saving
-- the result to a file for off-line analysis, for instance if you have an SMT solver that's not natively
-- supported out-of-the box by the SBV library. It takes two booleans:
--
--    * smtLib2: If 'True', will generate SMT-Lib2 output, otherwise SMT-Lib1 output
--
--    * isSat  : If 'True', will translate it as a SAT query, i.e., in the positive. If 'False', will
--               translate as a PROVE query, i.e., it will negate the result. (In this case, the check-sat
--               call to the SMT solver will produce UNSAT if the input is a theorem, as usual.)
compileToSMTLib :: Bool   -- ^ If True, output SMT-Lib2, otherwise SMT-Lib1
                -> Bool   -- ^ If True, translate directly, otherwise negate the goal. (Use True for SAT queries, False for PROVE queries.)
                -> Symbolic SVal
                -> IO String
compileToSMTLib smtLib2 isSat s = SBV.compileToSMTLib smtLib2 isSat (fmap toSBool s)

-- | Create both SMT-Lib1 and SMT-Lib2 benchmarks. The first argument is the basename of the file,
-- SMT-Lib1 version will be written with suffix ".smt1" and SMT-Lib2 version will be written with
-- suffix ".smt2". The 'Bool' argument controls whether this is a SAT instance, i.e., translate the query
-- directly, or a PROVE instance, i.e., translate the negated query. (See the second boolean argument to
-- 'compileToSMTLib' for details.)
generateSMTBenchmarks :: Bool -> FilePath -> Symbolic SVal -> IO ()
generateSMTBenchmarks isSat f s = SBV.generateSMTBenchmarks isSat f (fmap toSBool s)

-- | Proves the predicate using the given SMT-solver
proveWith :: SMTConfig -> Symbolic SVal -> IO ThmResult
proveWith cfg s = SBV.proveWith cfg (fmap toSBool s)

-- | Find a satisfying assignment using the given SMT-solver
satWith :: SMTConfig -> Symbolic SVal -> IO SatResult
satWith cfg s = SBV.satWith cfg (fmap toSBool s)

-- | Prove a property with multiple solvers, running them in separate threads. The
-- results will be returned in the order produced.
proveWithAll :: [SMTConfig] -> Symbolic SVal -> IO [(Solver, ThmResult)]
proveWithAll cfgs s = SBV.proveWithAll cfgs (fmap toSBool s)

-- | Prove a property with multiple solvers, running them in separate
-- threads. Only the result of the first one to finish will be
-- returned, remaining threads will be killed.
proveWithAny :: [SMTConfig] -> Symbolic SVal -> IO (Solver, ThmResult)
proveWithAny cfgs s = SBV.proveWithAny cfgs (fmap toSBool s)

-- | Find a satisfying assignment to a property with multiple solvers,
-- running them in separate threads. The results will be returned in
-- the order produced.
satWithAll :: [SMTConfig] -> Symbolic SVal -> IO [(Solver, SatResult)]
satWithAll cfgs s = SBV.satWithAll cfgs (fmap toSBool s)

-- | Find a satisfying assignment to a property with multiple solvers,
-- running them in separate threads. Only the result of the first one
-- to finish will be returned, remaining threads will be killed.
satWithAny :: [SMTConfig] -> Symbolic SVal -> IO (Solver, SatResult)
satWithAny cfgs s = SBV.satWithAny cfgs (fmap toSBool s)

-- | Find all satisfying assignments to a property with multiple
-- solvers, running them in separate threads. Only the result of the
-- first one to finish will be returned, remaining threads will be
-- killed.
allSatWithAll :: [SMTConfig] -> Symbolic SVal -> IO [(Solver, AllSatResult)]
allSatWithAll cfgs s = SBV.allSatWithAll cfgs (fmap toSBool s)

-- | Find all satisfying assignments to a property with multiple
-- solvers, running them in separate threads. Only the result of the
-- first one to finish will be returned, remaining threads will be
-- killed.
allSatWithAny :: [SMTConfig] -> Symbolic SVal -> IO (Solver, AllSatResult)
allSatWithAny cfgs s = SBV.allSatWithAny cfgs (fmap toSBool s)

-- | Extract a model, the result is a tuple where the first argument (if True)
-- indicates whether the model was "probable". (i.e., if the solver returned unknown.)
getModel :: SMTResult -> Either String (Bool, [CW])
getModel = SBV.getModel

-- | Extract a model dictionary. Extract a dictionary mapping the variables to
-- their respective values as returned by the SMT solver. Also see `getModelDictionaries`.
getModelDictionary :: SMTResult -> Map String CW
getModelDictionary = SBV.getModelDictionary
