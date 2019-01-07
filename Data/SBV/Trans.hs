-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Trans
-- Author    : Brian Schroeder, Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- More generalized alternative to @Data.SBV@ for advanced client use
-----------------------------------------------------------------------------

module Data.SBV.Trans (
  -- * Symbolic types

  -- ** Booleans
    SBool
  -- *** Boolean values and functions
  , sTrue, sFalse, sNot, (.&&), (.||), (.<+>), (.~&), (.~|), (.=>), (.<=>), fromBool, oneIf
  -- *** Logical functions
  , sAnd, sOr, sAny, sAll
  -- ** Bit-vectors
  -- *** Unsigned bit-vectors
  , SWord8, SWord16, SWord32, SWord64
  -- *** Signed bit-vectors
  , SInt8, SInt16, SInt32, SInt64
  -- ** Unbounded integers
  , SInteger
  -- ** Floating point numbers
  , SFloat, SDouble
  -- ** Algebraic reals
  , SReal, AlgReal, sRealToSInteger
  -- ** Characters, Strings and Regular Expressions
  , SChar, SString
  -- ** Symbolic lists
  , SList
  -- * Arrays of symbolic values
  , SymArray(newArray_, newArray, readArray, writeArray, mergeArrays), SArray, SFunArray

  -- * Creating symbolic values
  -- ** Single value
  , sBool, sWord8, sWord16, sWord32, sWord64, sInt8, sInt16, sInt32, sInt64, sInteger, sReal, sFloat, sDouble, sChar, sString, sList

  -- ** List of values
  , sBools, sWord8s, sWord16s, sWord32s, sWord64s, sInt8s, sInt16s, sInt32s, sInt64s, sIntegers, sReals, sFloats, sDoubles, sChars, sStrings, sLists

  -- * Symbolic Equality and Comparisons
  , EqSymbolic(..), OrdSymbolic(..), Equality(..)
  -- * Conditionals: Mergeable values
  , Mergeable(..), ite, iteLazy

  -- * Symbolic integral numbers
  , SIntegral
  -- * Division and Modulus
  , SDivisible(..)
  -- * Bit-vector operations
  -- ** Conversions
  , sFromIntegral
  -- ** Shifts and rotates
  , sShiftLeft, sShiftRight, sRotateLeft, sRotateRight, sSignedShiftArithRight
  -- ** Finite bit-vector operations
  , SFiniteBits(..)
  -- ** Splitting, joining, and extending
  , Splittable(..)
  -- ** Exponentiation
  , (.^)
  -- * IEEE-floating point numbers
  , IEEEFloating(..), RoundingMode(..), SRoundingMode, nan, infinity, sNaN, sInfinity
  -- ** Rounding modes
  , sRoundNearestTiesToEven, sRoundNearestTiesToAway, sRoundTowardPositive, sRoundTowardNegative, sRoundTowardZero, sRNE, sRNA, sRTP, sRTN, sRTZ
  -- ** Conversion to/from floats
  , IEEEFloatConvertable(..)
  -- ** Bit-pattern conversions
  , sFloatAsSWord32, sWord32AsSFloat, sDoubleAsSWord64, sWord64AsSDouble, blastSFloat, blastSDouble

  -- * Enumerations
  , mkSymbolicEnumeration

  -- * Uninterpreted sorts, constants, and functions
  , Uninterpreted(..), addAxiom

  -- * Properties, proofs, and satisfiability
  , Predicate, Goal, MProvable(..), Provable, proveWithAll, proveWithAny , satWithAll
  , satWithAny, generateSMTBenchmark
  , solve
  -- * Constraints
  -- ** General constraints
  , constrain, softConstrain

  -- ** Constraint Vacuity

  -- ** Named constraints and attributes
  , namedConstraint, constrainWithAttribute

  -- ** Unsat cores

  -- ** Cardinality constraints
  , pbAtMost, pbAtLeast, pbExactly, pbLe, pbGe, pbEq, pbMutexed, pbStronglyMutexed

  -- * Checking safety
  , sAssert, isSafe, SExecutable(..)

  -- * Quick-checking
  , sbvQuickCheck

  -- * Optimization

  -- ** Multiple optimization goals
  , OptimizeStyle(..)
  -- ** Objectives
  , Objective(..), Metric(..)
  -- ** Soft assumptions
  , assertWithPenalty , Penalty(..)
  -- ** Field extensions
  -- | If an optimization results in an infinity/epsilon value, the returned `CV` value will be in the corresponding extension field.
  , ExtCV(..), GeneralizedCV(..)

  -- * Model extraction

  -- ** Inspecting proof results
  , ThmResult(..), SatResult(..), AllSatResult(..), SafeResult(..), OptimizeResult(..), SMTResult(..), SMTReasonUnknown(..)

  -- ** Observing expressions
  , observe

  -- ** Programmable model extraction
  , SatModel(..), Modelable(..), displayModels, extractModels
  , getModelDictionaries, getModelValues, getModelUninterpretedValues

  -- * SMT Interface
  , SMTConfig(..), Timing(..), SMTLibVersion(..), Solver(..), SMTSolver(..)
  -- ** Controlling verbosity

  -- ** Solvers
  , boolector, cvc4, yices, z3, mathSAT, abc
  -- ** Configurations
  , defaultSolverConfig, defaultSMTCfg, sbvCheckSolverInstallation, sbvAvailableSolvers
  , setLogic, Logic(..), setOption, setInfo, setTimeOut
  -- ** SBV exceptions
  , SBVException(..)

  -- * Abstract SBV type
  , SBV, HasKind(..), Kind(..), SymVal(..)
  , MonadSymbolic(..), Symbolic, SymbolicT, label, output, runSMT, runSMTWith

  -- * Module exports

  , module Data.Bits
  , module Data.Word
  , module Data.Int
  , module Data.Ratio
  ) where

import Data.SBV.Core.AlgReals
import Data.SBV.Core.Data
import Data.SBV.Core.Model
import Data.SBV.Core.Floating
import Data.SBV.Core.Splittable
import Data.SBV.Core.Symbolic

import Data.SBV.Provers.Prover

import Data.SBV.Client

import Data.SBV.Utils.TDiff   (Timing(..))

import Data.Bits
import Data.Int
import Data.Ratio
import Data.Word

import Data.SBV.SMT.Utils (SBVException(..))
import Data.SBV.Control.Types (SMTReasonUnknown(..), Logic(..))
