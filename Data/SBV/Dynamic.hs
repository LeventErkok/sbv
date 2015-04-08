---------------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Dynamic
-- Copyright   :  (c) Levent Erkok
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
  -- $progIntro
  -- ** Symbolic types
  -- *** Abstract symbolic value type
    SVal
  , CW(..)
  , Kind(..)
  , svKind, svBitSize, svSigned
  -- *** Arrays of symbolic values
  , SArr
  , readSArr, resetSArr, writeSArr, mergeSArr, newSArr, eqSArr

  -- ** Creating a symbolic variable
  -- $createSym
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
  -- * Uninterpreted sorts, constants, and functions
  -- $uninterpreted
  , svUninterpreted
  -- * Model extraction
  -- $modelExtraction

  -- ** Inspecting proof results
  -- $resultTypes
  , ThmResult(..), SatResult(..), AllSatResult(..), SMTResult(..), SafeResult(..)
  -- * SMT Interface: Configurations and solvers
  , SMTConfig(..), SMTLibLogic(..), Logic(..), OptimizeOpts(..), Solver(..), SMTSolver(..), boolector, cvc4, yices, z3, mathSAT, abc, defaultSolverConfig, sbvCurrentSolver, defaultSMTCfg, sbvCheckSolverInstallation, sbvAvailableSolvers

  -- * Symbolic computations
  , outputSVal{-, SymWord(..)-}

  -- * Getting SMT-Lib output (for offline analysis)
  , svCompileToSMTLib{-, generateSMTBenchmarks-}
  -- * Code generation from symbolic programs
  -- $cCodeGeneration
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
  -- $unboundedCGen
  , cgIntegerSize, cgSRealType, CgSRealType(..)

  -- ** Compilation to C
  , compileToC, compileToCLib
  ) where

import Data.SBV.BitVectors.Kind
import Data.SBV.BitVectors.Concrete
import Data.SBV.BitVectors.Symbolic
import Data.SBV.BitVectors.Operations

import Data.SBV.Compilers.CodeGen ( SBVCodeGen
                                  , svCgInput, svCgInputArr
                                  , svCgOutput, svCgOutputArr
                                  , svCgReturn, svCgReturnArr
                                  , cgPerformRTCs, cgSetDriverValues, cgGenerateDriver, cgGenerateMakefile
                                  , cgAddPrototype, cgAddDecl, cgAddLDFlags
                                  , cgIntegerSize, cgSRealType, CgSRealType(..)
                                  )
import Data.SBV.Compilers.C       (compileToC, compileToCLib)
import Data.SBV.Provers.Prover    (boolector, cvc4, yices, z3, mathSAT, abc, defaultSMTCfg, svCompileToSMTLib)
import Data.SBV.SMT.SMT           (ThmResult(..), SatResult(..), AllSatResult(..), SafeResult(..))
import Data.SBV.Tools.Optimize    (OptimizeOpts(..))
import Data.SBV                   (sbvCurrentSolver, sbvCheckSolverInstallation, defaultSolverConfig, sbvAvailableSolvers)
