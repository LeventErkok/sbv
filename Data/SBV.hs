-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- (The sbv library is hosted at <http://github.com/LeventErkok/sbv>.
-- Comments, bug reports, and patches are always welcome.)
--
-- SBV: SMT Based Verification
--
-- Express properties about Haskell programs and automatically prove
-- them using SMT solvers.
--
-- >>> prove $ \x -> x `shiftL` 2 .== 4 * (x :: SWord8)
-- Q.E.D.
--
-- >>> prove $ \x -> x `shiftL` 2 .== 2 * (x :: SWord8)
-- Falsifiable. Counter-example:
--   s0 = 64 :: Word8
--
-- And similarly, 'sat' finds a satisfying instance. The types involved are:
--
-- @
--     'prove' :: 'Provable' a => a -> 'IO' 'ThmResult'
--     'sat'   :: 'Data.SBV.Provers.Satisfiable' a => a -> 'IO' 'SatResult'
-- @
--
-- The classes 'Provable' and 'Data.SBV.Provers.Satisfiable' come with instances for n-ary predicates, for arbitrary n.
-- The predicates are just regular Haskell functions over symbolic types listed below.
-- Functions for checking satisfiability ('sat' and 'allSat') are also
-- provided.
--
-- The sbv library introduces the following symbolic types:
--
--   * 'SBool': Symbolic Booleans (bits).
--
--   * 'SWord8', 'SWord16', 'SWord32', 'SWord64': Symbolic Words (unsigned).
--
--   * 'SInt8',  'SInt16',  'SInt32',  'SInt64': Symbolic Ints (signed).
--
--   * 'SWord' @n@: Generalized symbolic words of arbitrary bit-size.
--
--   * 'SInt' @n@: Generalized symbolic ints of arbitrary bit-size.
--
--   * 'SInteger': Unbounded signed integers.
--
--   * 'SReal': Algebraic-real numbers.
--
--   * 'SFloat': IEEE-754 single-precision floating point values.
--
--   * 'SDouble': IEEE-754 double-precision floating point values.
--
--   * 'SRational': Rationals. (Ratio of two symbolic integers.)
--
--   * 'SFloatingPoint': Generalized IEEE-754 floating point values, with user specified exponent and
--   mantissa widths.
--
--   * 'SChar', 'SString', 'RegExp': Characters, strings and regular expressions.
--
--   * 'SList': Symbolic lists (which can be nested)
--
--   * 'STuple', 'STuple2', 'STuple3', .., 'STuple8' : Symbolic tuples (upto 8-tuples, can be nested)
--
--   * 'SEither': Symbolic sums
--
--   * 'SMaybe': Symbolic optional values.
--
--   * 'SSet': Symbolic sets.
--
--   * 'SArray': Arrays of symbolic values.
--
--   * Symbolic polynomials over GF(2^n), polynomial arithmetic, and CRCs.
--
--   * Uninterpreted constants and functions over symbolic values, with user
--     defined SMT-Lib axioms.
--
--   * Uninterpreted sorts, and proofs over such sorts, potentially with axioms.
--
--   * Ability to define SMTLib functions, generated directly from Haskell versions,
--     including support for recursive and mutually recursive functions.
--
--   * Express quantified formulas (both universals and existentials, including
--     alternating quantifiers), covering first-order logic.
--
--   * Model validation: SBV can validate models returned by solvers, which allows
--     for protection against bugs in SMT solvers and SBV itself. (See the 'validateModel'
--     parameter.)
--
-- The user can construct ordinary Haskell programs using these types, which behave
-- very similar to their concrete counterparts. In particular these types belong to the
-- standard classes 'Num', 'Bits', custom versions of 'Eq' ('EqSymbolic')
-- and 'Ord' ('OrdSymbolic'), along with several other custom classes for simplifying
-- programming with symbolic values. The framework takes full advantage of Haskell's type
-- inference to avoid many common mistakes.
--
-- Furthermore, predicates (i.e., functions that return 'SBool') built out of
-- these types can also be:
--
--   * proven correct via an external SMT solver (the 'prove' function)
--
--   * checked for satisfiability (the 'sat', 'allSat' functions)
--
--   * used in synthesis (the `sat` function with existentials)
--
--   * quick-checked
--
-- If a predicate is not valid, 'prove' will return a counterexample: An
-- assignment to inputs such that the predicate fails. The 'sat' function will
-- return a satisfying assignment, if there is one. The 'allSat' function returns
-- all satisfying assignments.
--
-- The sbv library uses third-party SMT solvers via the standard SMT-Lib interface:
-- <http://smtlib.cs.uiowa.edu/>
--
-- The SBV library is designed to work with any SMT-Lib compliant SMT-solver.
-- Currently, we support the following SMT-Solvers out-of-the box:
--
--   * ABC from University of Berkeley: <http://www.eecs.berkeley.edu/~alanmi/abc/>
--
--   * CVC4, and CVC5 from Stanford University and the University of Iowa. <https://cvc4.github.io/> and <https://cvc5.github.io>
--
--   * Boolector from Johannes Kepler University: <https://boolector.github.io> and its successor Bitwuzla from Stanford
--     university: <https://bitwuzla.github.io>
--
--   * MathSAT from Fondazione Bruno Kessler and DISI-University of Trento: <http://mathsat.fbk.eu/>
--
--   * Yices from SRI: <http://yices.csl.sri.com/>
--
--   * DReal from CMU: <http://dreal.github.io/>
--
--   * OpenSMT from Università della Svizzera italiana <https://verify.inf.usi.ch/opensmt>
--
--   * Z3 from Microsoft: <http://github.com/Z3Prover/z3/wiki>
--
-- SBV requires recent versions of these solvers; please see the file
-- @SMTSolverVersions.md@ in the source distribution for specifics.
--
-- SBV also allows calling these solvers in parallel, either getting results from multiple solvers
-- or returning the fastest one. (See 'proveWithAll', 'proveWithAny', etc.)
--
-- Support for other compliant solvers can be added relatively easily, please
-- get in touch if there is a solver you'd like to see included.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV (
  -- $progIntro

  -- * Symbolic types

  -- ** Booleans
    SBool
  -- *** Boolean values and functions
  , sTrue, sFalse, sNot, (.&&), (.||), (.<+>), (.~&), (.~|), (.=>), (.<=>), fromBool, oneIf
  -- *** Logical aggregations
  , sAnd, sOr, sAny, sAll
  -- ** Bit-vectors
  -- *** Unsigned bit-vectors
  , SWord8, SWord16, SWord32, SWord64, SWord, WordN
  -- *** Signed bit-vectors
  , SInt8, SInt16, SInt32, SInt64, SInt, IntN
  -- *** Converting between fixed-size and arbitrary bitvectors
  , BVIsNonZero, FromSized, ToSized, fromSized, toSized
  -- ** Unbounded integers
  -- $unboundedLimitations
  , SInteger
  -- ** Floating point numbers
  -- $floatingPoints
  , ValidFloat, SFloat, SDouble
  , SFloatingPoint, FloatingPoint
  , SFPHalf, FPHalf
  , SFPBFloat, FPBFloat
  , SFPSingle, FPSingle
  , SFPDouble, FPDouble
  , SFPQuad, FPQuad
  -- ** Rationals
  , SRational
  -- ** Algebraic reals
  -- $algReals
  , SReal, AlgReal(..), sRealToSInteger, algRealToRational, RealPoint(..), realPoint, RationalCV(..)
  -- ** Characters, Strings and Regular Expressions
  -- $strings
  , SChar, SString
  -- ** Symbolic lists
  -- $lists
  , SList
  -- ** Tuples
  -- $tuples
  , SymTuple, STuple, STuple2, STuple3, STuple4, STuple5, STuple6, STuple7, STuple8
  -- ** Sum types
  , SMaybe, SEither
  -- ** Sets
  , RCSet(..), SSet
  -- * Arrays of symbolic values
  , SymArray(readArray, writeArray, mergeArrays, sListArray), newArray_, newArray, SArray, lambdaAsArray

  -- * Creating symbolic values
  -- ** Single value
  -- $createSym
  , sBool, sBool_
  , sWord8, sWord8_, sWord16, sWord16_, sWord32, sWord32_, sWord64, sWord64_, sWord, sWord_
  , sInt8,  sInt8_,  sInt16,  sInt16_,  sInt32,  sInt32_,  sInt64,  sInt64_, sInt, sInt_
  , sInteger, sInteger_
  , sReal, sReal_
  , sRational, sRational_
  , sFloat, sFloat_
  , sDouble, sDouble_
  , sFloatingPoint, sFloatingPoint_
  , sFPHalf, sFPHalf_
  , sFPBFloat, sFPBFloat_
  , sFPSingle, sFPSingle_
  , sFPDouble, sFPDouble_
  , sFPQuad, sFPQuad_
  , sChar, sChar_
  , sString, sString_
  , sList, sList_
  , sTuple, sTuple_
  , sEither, sEither_
  , sMaybe, sMaybe_
  , sSet, sSet_

  -- ** List of values
  -- $createSyms
  , sBools
  , sWord8s, sWord16s, sWord32s, sWord64s, sWords
  , sInt8s,  sInt16s,  sInt32s,  sInt64s, sInts
  , sIntegers
  , sReals
  , sRationals
  , sFloats
  , sDoubles
  , sFloatingPoints
  , sFPHalfs
  , sFPBFloats
  , sFPSingles
  , sFPDoubles
  , sFPQuads
  , sChars
  , sStrings
  , sLists
  , sTuples
  , sEithers
  , sMaybes
  , sSets

  -- * Symbolic Equality and Comparisons
  -- $distinctNote
  , EqSymbolic(..), OrdSymbolic(..), Equality(..)
  -- * Conditionals: Mergeable values
  , Mergeable(..), ite, iteLazy

  -- * Symbolic integral numbers
  , SIntegral
  -- * Division and Modulus
  , SDivisible(..)
  -- $euclidianNote
  , sEDivMod, sEDiv, sEMod
  -- * Bit-vector operations
  -- ** Conversions
  , sFromIntegral
  -- ** Shifts and rotates
  -- $shiftRotate
  , sShiftLeft, sShiftRight, sRotateLeft, sBarrelRotateLeft, sRotateRight, sBarrelRotateRight, sSignedShiftArithRight
  -- ** Finite bit-vector operations
  , SFiniteBits(..)
  -- ** Splitting, joining, and extending bit-vectors
  , bvExtract, (#), zeroExtend, signExtend, bvDrop, bvTake, ByteConverter(..)
  -- ** Exponentiation
  , (.^)
  -- * IEEE-floating point numbers
  , IEEEFloating(..), RoundingMode(..), SRoundingMode, nan, infinity, sNaN, sInfinity
  -- ** Rounding modes
  , sRoundNearestTiesToEven, sRoundNearestTiesToAway, sRoundTowardPositive, sRoundTowardNegative, sRoundTowardZero, sRNE, sRNA, sRTP, sRTN, sRTZ
  -- ** Conversion to/from floats
  -- $conversionNote
  , IEEEFloatConvertible(..)

  -- ** Bit-pattern conversions
  , sFloatAsSWord32,       sWord32AsSFloat
  , sDoubleAsSWord64,      sWord64AsSDouble
  , sFloatingPointAsSWord, sWordAsSFloatingPoint

  -- ** Extracting bit patterns from floats
  , blastSFloat
  , blastSDouble
  , blastSFloatingPoint

  -- ** Showing values in detail
  , crack

  -- * Enumerations
  -- $enumerations
  , mkSymbolicEnumeration

  -- * Uninterpreted sorts, constants, and functions
  -- $uninterpreted
  , mkUninterpretedSort

  -- * Stopping unrolling: Defined functions
  , SMTDefinable(..)

  -- * Special relations
  -- $specialRels
  , Relation, isPartialOrder, isLinearOrder, isTreeOrder, isPiecewiseLinearOrder, mkTransitiveClosure

  -- * Properties, proofs, and satisfiability
  -- $proveIntro
  -- $multiIntro
  , Predicate, ConstraintSet, Provable, Satisfiable
  , prove, proveWith
  , dprove, dproveWith
  , sat, satWith
  , dsat, dsatWith
  , allSat, allSatWith
  , optimize, optimizeWith
  , isVacuousProof, isVacuousProofWith
  , isTheorem, isTheoremWith, isSatisfiable, isSatisfiableWith
  , proveWithAny, proveWithAll, proveConcurrentWithAny, proveConcurrentWithAll
  , satWithAny,   satWithAll,   satConcurrentWithAny,   satConcurrentWithAll
  , generateSMTBenchmarkSat, generateSMTBenchmarkProof
  , solve
  -- ** Partitioning result space
  -- $partitionIntro
  , partition

  -- * Constraints and Quantifiers
  -- $constrainIntro
  -- ** General constraints
  -- $generalConstraints
  , constrain, softConstrain

  -- ** Quantified constraints, quantifier elimination, and skolemization
  -- $quantifiers
  , QuantifiedBool, quantifiedBool, Forall(..), Exists(..), ExistsUnique(..), ForallN(..), ExistsN(..), QNot(..), Skolemize(..)

  -- ** Constraint Vacuity
  -- $constraintVacuity

  -- ** Named constraints and attributes
  -- $namedConstraints
  , namedConstraint, constrainWithAttribute

  -- ** Unsat cores
  -- $unsatCores

  -- ** Cardinality constraints
  -- $cardIntro
  , pbAtMost, pbAtLeast, pbExactly, pbLe, pbGe, pbEq, pbMutexed, pbStronglyMutexed

  -- * Checking safety
  -- $safeIntro
  , sAssert, isSafe, SExecutable, sName, safe, safeWith

  -- * Quick-checking
  , sbvQuickCheck

  -- * Optimization
  -- $optiIntro

  -- ** Multiple optimization goals
  -- $multiOpt
  , OptimizeStyle(..)
  -- ** Objectives and Metrics
  , Objective(..)
  , Metric(..), minimize, maximize
  -- ** Soft assertions
  -- $softAssertions
  , assertWithPenalty , Penalty(..)
  -- ** Field extensions
  -- | If an optimization results in an infinity/epsilon value, the returned `CV` value will be in the corresponding extension field.
  , ExtCV(..), GeneralizedCV(..)

  -- * Model extraction
  -- $modelExtraction

  -- ** Inspecting proof results
  -- $resultTypes
  , ThmResult(..), SatResult(..), AllSatResult(..), SafeResult(..), OptimizeResult(..), SMTResult(..), SMTReasonUnknown(..)

  -- ** Observing expressions
  -- $observeInternal
  , observe, observeIf, sObserve

  -- ** Programmable model extraction
  -- $programmableExtraction
  , SatModel(..), Modelable(..), displayModels, extractModels
  , getModelDictionaries, getModelValues, getModelUninterpretedValues

  -- * SMT Interface
  , SMTConfig(..), Timing(..), SMTLibVersion(..), Solver(..), SMTSolver(..)
  -- ** Controlling verbosity
  -- $verbosity

  -- ** Solvers
  , boolector, bitwuzla, cvc4, cvc5, yices, dReal, z3, mathSAT, abc, openSMT
  -- ** Configurations
  , defaultSolverConfig, defaultSMTCfg, defaultDeltaSMTCfg, sbvCheckSolverInstallation, getAvailableSolvers
  , setLogic, Logic(..), setOption, setInfo, setTimeOut
  -- ** SBV exceptions
  , SBVException(..)

  -- * Abstract SBV type
  , SBV, HasKind(..), Kind(..)
  , SymVal, free, free_, mkFreeVars, symbolic, symbolics, literal, unliteral, fromCV
  , isConcrete, isSymbolic, isConcretely, mkSymVal
  , MonadSymbolic(..), Symbolic, SymbolicT, label, output, runSMT, runSMTWith

  -- * Module exports
  -- $moduleExportIntro

  , module Data.Bits
  , module Data.Word
  , module Data.Int
  , module Data.Ratio
  ) where

import Control.Monad (when)

import Data.SBV.Core.AlgReals
import Data.SBV.Core.Data       hiding (free, free_, mkFreeVars,
                                        output, symbolic, symbolics, mkSymVal,
                                        newArray, newArray_)
import Data.SBV.Core.Model      hiding (assertWithPenalty, minimize, maximize,
                                        solve, sBool, sBool_, sBools, sChar, sChar_, sChars,
                                        sDouble, sDouble_, sDoubles, sFloat, sFloat_, sFloats,
                                        sFloatingPoint, sFloatingPoint_, sFloatingPoints,
                                        sFPHalf, sFPHalf_, sFPHalfs, sFPBFloat, sFPBFloat_, sFPBFloats, sFPSingle, sFPSingle_, sFPSingles,
                                        sFPDouble, sFPDouble_, sFPDoubles, sFPQuad, sFPQuad_, sFPQuads,
                                        sInt8, sInt8_, sInt8s, sInt16, sInt16_, sInt16s, sInt32, sInt32_, sInt32s,
                                        sInt64, sInt64_, sInt64s, sInteger, sInteger_, sIntegers,
                                        sList, sList_, sLists, sTuple, sTuple_, sTuples,
                                        sReal, sReal_, sReals, sString, sString_, sStrings,
                                        sRational, sRational_, sRationals,
                                        sWord8, sWord8_, sWord8s, sWord16, sWord16_, sWord16s,
                                        sWord32, sWord32_, sWord32s, sWord64, sWord64_, sWord64s,
                                        sMaybe, sMaybe_, sMaybes, sEither, sEither_, sEithers, sSet, sSet_, sSets,
                                        sBarrelRotateLeft, sBarrelRotateRight)

import qualified Data.SBV.Core.Model as M (sBarrelRotateLeft, sBarrelRotateRight)

import           Data.SBV.Core.Sized       hiding (sWord, sWord_, sWords, sInt, sInt_, sInts, bvExtract, (#), zeroExtend, signExtend, bvDrop, bvTake)
import qualified Data.SBV.Core.Sized as CS

import Data.SBV.Core.Kind

import Data.SBV.Core.SizedFloats

import Data.SBV.Core.Floating
import Data.SBV.Core.Symbolic   ( MonadSymbolic(..), SymbolicT, registerKind
                                , ProgInfo(..), rProgInfo, SpecialRelOp(..), UICodeKind(UINone)
                                , getRootState
                                )

import Data.SBV.Provers.Prover hiding (prove, proveWith, sat, satWith, allSat,
                                       dsat, dsatWith, dprove, dproveWith,
                                       allSatWith, optimize, optimizeWith,
                                       isVacuousProof, isVacuousProofWith,
                                       isTheorem, isTheoremWith, isSatisfiable,
                                       isSatisfiableWith, runSMT, runSMTWith,
                                       sName, safe, safeWith)

import Data.IORef (modifyIORef', readIORef)

import Data.SBV.Client
import Data.SBV.Client.BaseIO

import Data.SBV.Utils.TDiff (Timing(..))

import Data.Bits
import Data.Int
import Data.Ratio
import Data.Word

import Data.SBV.SMT.Utils (SBVException(..))
import Data.SBV.Control.Types (SMTReasonUnknown(..), Logic(..))

import qualified Data.SBV.Utils.CrackNum as CN

import Data.Proxy (Proxy(..))
import GHC.TypeLits (KnownNat, type (<=), type (+), type (-))

import Prelude hiding((+), (-)) -- to avoid the haddock ambiguity

import Data.Char (isSpace, isPunctuation)

--- $setup
--- >>> -- For doctest purposes only:
--- >>> :set -XDataKinds
--- >>> import Data.Proxy

-- | Show a value in detailed (cracked) form, if possible.
-- This makes most sense with numbers, and especially floating-point types.
crack :: Bool -> SBV a -> String
crack verb (SBV (SVal _ (Left cv))) | Just s <- CN.crackNum cv verb Nothing = s
crack _    (SBV sv)                                                         = show sv

-- Haddock section documentation
{- $progIntro
The SBV library is really two things:

  * A framework for writing symbolic programs in Haskell, i.e., programs operating on
    symbolic values along with the usual concrete counterparts.

  * A framework for proving properties of such programs using SMT solvers.

The programming goal of SBV is to provide a /seamless/ experience, i.e., let people program
in the usual Haskell style without distractions of symbolic coding. While Haskell helps
in some aspects (the 'Num' and 'Bits' classes simplify coding), it makes life harder
in others. For instance, @if-then-else@ only takes 'Bool' as a test in Haskell, and
comparisons ('>' etc.) only return 'Bool's. Clearly we would like these values to be
symbolic (i.e., 'SBool'), thus stopping us from using some native Haskell constructs.
When symbolic versions of operators are needed, they are typically obtained by prepending a dot,
for instance '==' becomes '.=='. Care has been taken to make the transition painless. In
particular, any Haskell program you build out of symbolic components is fully concretely
executable within Haskell, without the need for any custom interpreters. (They are truly
Haskell programs, not AST's built out of pieces of syntax.) This provides for an integrated
feel of the system, one of the original design goals for SBV.

Incremental query mode: SBV provides a wide variety of ways to utilize SMT-solvers, without requiring the user to
deal with the solvers themselves. While this mode is convenient, advanced users might need
access to the underlying solver at a lower level. For such use cases, SBV allows
users to have an interactive session: The user can issue commands to the solver, inspect
the values/results, and formulate new constraints. This advanced feature is available through
the "Data.SBV.Control" module, where most SMTLib features are made available via a typed-API.
-}

{- $proveIntro
The SBV library provides a "push-button" verification system via automated SMT solving. The
design goal is to let SMT solvers be used without any knowledge of how SMT solvers work
or how different logics operate. The details are hidden behind the SBV framework, providing
Haskell programmers with a clean API that is unencumbered by the details of individual solvers.
To that end, we use the SMT-Lib standard (<http://smtlib.cs.uiowa.edu/>)
to communicate with arbitrary SMT solvers.
-}

{- $multiIntro
=== Using multiple solvers
On a multi-core machine, it might be desirable to try a given property using multiple SMT solvers,
using parallel threads. Even with machines with single-cores, threading can be helpful if you
want to try out multiple-solvers but do not know which one would work the best
for the problem at hand ahead of time.

SBV allows proving/satisfiability-checking with multiple
backends at the same time. Each function comes in two variants, one that
returns the results from all solvers, the other that returns the fastest one.

The @All@ variants, (i.e., 'proveWithAll', 'satWithAll') run all solvers and
return all the results. SBV internally makes sure that the result is lazily generated; so,
the order of solvers given does not matter. In other words, the order of results will follow
the order of the solvers as they finish, not as given by the user. These variants are useful when you
want to make sure multiple-solvers agree (or disagree!) on a given problem.

The @Any@ variants, (i.e., 'proveWithAny', 'satWithAny') will run all the solvers
in parallel, and return the results of the first one finishing. The other threads will then be killed. These variants
are useful when you do not care if the solvers produce the same result, but rather want to get the
solution as quickly as possible, taking advantage of modern many-core machines.

Note that the function 'getAvailableSolvers' will return all the installed solvers, which can be
used as the first argument to all these functions, if you simply want to try all available solvers on a machine.
-}

{- $safeIntro

The 'sAssert' function allows users to introduce invariants to make sure
certain properties hold at all times. This is another mechanism to provide further documentation/contract info
into SBV code. The functions 'safe' and 'safeWith' can be used to statically discharge these proof assumptions.
If a violation is found, SBV will print a model showing which inputs lead to the invariant being violated.

Here's a simple example. Let's assume we have a function that does subtraction, and requires its
first argument to be larger than the second:

>>> let sub x y = sAssert Nothing "sub: x >= y must hold!" (x .>= y) (x - y)

Clearly, this function is not safe, as there's nothing that stops us from passing it a larger second argument.
We can use 'safe' to statically see if such a violation is possible before we use this function elsewhere.

>>> safe (sub :: SInt8 -> SInt8 -> SInt8)
[sub: x >= y must hold!: Violated. Model:
  s0 = 0 :: Int8
  s1 = 1 :: Int8]

What happens if we make sure to arrange for this invariant? Consider this version:

>>> let safeSub x y = ite (x .>= y) (sub x y) 0

Clearly, @safeSub@ must be safe. And indeed, SBV can prove that:

>>> safe (safeSub :: SInt8 -> SInt8 -> SInt8)
[sub: x >= y must hold!: No violations detected]

Note how we used @sub@ and @safeSub@ polymorphically. We only need to monomorphise our types when a proof
attempt is done, as we did in the 'safe' calls.

If required, the user can pass a @CallStack@ through the first argument to 'sAssert', which will be used
by SBV to print a diagnostic info to pinpoint the failure.

Also see "Documentation.SBV.Examples.Misc.NoDiv0" for the classic div-by-zero example.
-}


{- $optiIntro
  SBV can optimize metric functions, i.e., those that generate both bounded @SIntN@, @SWordN@, and unbounded 'SInteger'
  types, along with those produce 'SReal's. That is, it can find models satisfying all the constraints while minimizing
  or maximizing user given metrics. Currently, optimization requires the use of the z3 SMT solver as the backend,
  and a good review of these features is given
  in this paper: <http://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/nbjorner-scss2014.pdf>.

  Goals can be lexicographically (default), independently, or pareto-front optimized. The relevant functions are:

      * 'minimize': Minimize a given arithmetic goal
      * 'maximize': Minimize a given arithmetic goal

  Goals can be optimized at a regular or an extended value: An extended value is either positive or negative infinity
  (for unbounded integers and reals) or positive or negative epsilon differential from a real value (for reals).

  For instance, a call of the form

       @ 'minimize' "name-of-goal" $ x + 2*y @

  minimizes the arithmetic goal @x+2*y@, where @x@ and @y@ can be signed\/unsigned bit-vectors, reals,
  or integers.

== A simple example

  Here's an optimization example in action:

  >>> optimize Lexicographic $ \x y -> minimize "goal" (x+2*(y::SInteger))
  Optimal in an extension field:
    goal = -oo :: Integer

  We will describe the role of the constructor 'Lexicographic' shortly.

  Of course, this becomes more useful when the result is not in an extension field:

>>> :{
    optimize Lexicographic $ do
                  x <- sInteger "x"
                  y <- sInteger "y"
                  constrain $ x .> 0
                  constrain $ x .< 6
                  constrain $ y .> 2
                  constrain $ y .< 12
                  minimize "goal" $ x + 2 * y
    :}
Optimal model:
  x    = 1 :: Integer
  y    = 3 :: Integer
  goal = 7 :: Integer

  As usual, the programmatic API can be used to extract the values of objectives and model-values ('getModelObjectives',
  'getModelAssignment', etc.) to access these values and program with them further.

  The following examples illustrate the use of basic optimization routines:

     * "Documentation.SBV.Examples.Optimization.LinearOpt": Simple linear-optimization example.
     * "Documentation.SBV.Examples.Optimization.Production": Scheduling machines in a shop
     * "Documentation.SBV.Examples.Optimization.VM": Scheduling virtual-machines in a data-center
-}

{- $multiOpt

  Multiple goals can be specified, using the same syntax. In this case, the user gets to pick what style of
  optimization to perform, by passing the relevant 'OptimizeStyle' as the first argument to 'optimize'.

    * ['Lexicographic']. The solver will optimize the goals in the given order, optimizing
      the latter ones under the model that optimizes the previous ones.

    * ['Independent']. The solver will optimize the goals independently of each other. In this case the user will
      be presented a model for each goal given.

    * ['Pareto']. Finally, the user can query for pareto-fronts. A pareto front is an model such that no goal can be made
      "better" without making some other goal "worse."

      Pareto fronts only make sense when the objectives are bounded. If there are unbounded objective values, then the
      backend solver can loop infinitely. (This is what z3 does currently.) If you are not sure the objectives are
      bounded, you should first use 'Independent' mode to ensure the objectives are bounded, and then switch to
      pareto-mode to extract them further.

      The optional number argument to 'Pareto' specifies the maximum number of pareto-fronts the user is asking
      to get. If 'Nothing', SBV will query for all pareto-fronts. Note that pareto-fronts can be really large,
      so if 'Nothing' is used, there is a potential for waiting indefinitely for the SBV-solver interaction to finish. (If
      you suspect this might be the case, run in 'verbose' mode to see the interaction and put a limiting factor
      appropriately.)
-}

{- $softAssertions

  Related to optimization, SBV implements soft-asserts via 'assertWithPenalty' calls. A soft assertion
  is a hint to the SMT solver that we would like a particular condition to hold if **possible*.
  That is, if there is a solution satisfying it, then we would like it to hold, but it can be violated
  if there is no way to satisfy it. Each soft-assertion can be associated with a numeric penalty for
  not satisfying it, hence turning it into an optimization problem.

  Note that 'assertWithPenalty' works well with optimization goals ('minimize'/'maximize' etc.),
  and are most useful when we are optimizing a metric and thus some of the constraints
  can be relaxed with a penalty to obtain a good solution. Again
  see <http://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/nbjorner-scss2014.pdf>
  for a good overview of the features in Z3 that SBV is providing the bridge for.

  A soft assertion can be specified in one of the following three main ways:

       @
         'assertWithPenalty' "bounded_x" (x .< 5) 'DefaultPenalty'
         'assertWithPenalty' "bounded_x" (x .< 5) ('Penalty' 2.3 Nothing)
         'assertWithPenalty' "bounded_x" (x .< 5) ('Penalty' 4.7 (Just "group-1")) @

  In the first form, we are saying that the constraint @x .< 5@ must be satisfied, if possible,
  but if this constraint can not be satisfied to find a model, it can be violated with the default penalty of 1.

  In the second case, we are associating a penalty value of @2.3@.

  Finally in the third case, we are also associating this constraint with a group. The group
  name is only needed if we have classes of soft-constraints that should be considered together.

-}

{- $modelExtraction
The default 'Show' instances for prover calls provide all the counter-example information in a
human-readable form and should be sufficient for most casual uses of sbv. However, tools built
on top of sbv will inevitably need to look into the constructed models more deeply, programmatically
extracting their results and performing actions based on them. The API provided in this section
aims at simplifying this task.
-}

{- $resultTypes
'ThmResult', 'SatResult', and 'AllSatResult' are simple newtype wrappers over 'SMTResult'. Their
main purpose is so that we can provide custom 'Show' instances to print results accordingly.
-}

{- $programmableExtraction
While default 'Show' instances are sufficient for most use cases, it is sometimes desirable (especially
for library construction) that the SMT-models are reinterpreted in terms of domain types. Programmable
extraction allows getting arbitrarily typed models out of SMT models.
-}

{- $moduleExportIntro
The SBV library exports the following modules wholesale, as user programs will have to import these
modules to make any sensible use of the SBV functionality.
-}

{- $createSym
These functions simplify declaring symbolic variables of various types. Strictly speaking, they are just synonyms
for 'free' (specialized at the given type), but they might be easier to use. We provide both the named and anonymous
versions, latter with the underscore suffix.
-}

{- $createSyms
These functions simplify declaring a sequence symbolic variables of various types. Strictly speaking, they are just synonyms
for 'mapM' 'free' (specialized at the given type), but they might be easier to use.
-}

{- $unboundedLimitations
The SBV library supports unbounded signed integers with the type 'SInteger', which are not subject to
overflow/underflow as it is the case with the bounded types, such as 'SWord8', 'SInt16', etc. However,
some bit-vector based operations are /not/ supported for the 'SInteger' type while in the verification mode. That
is, you can use these operations on 'SInteger' values during normal programming/simulation.
but the SMT translation will not support these operations since there corresponding operations are not supported in SMT-Lib.
Note that this should rarely be a problem in practice, as these operations are mostly meaningful on fixed-size
bit-vectors. The operations that are restricted to bounded word/int sizes are:

   * Rotations and shifts: 'rotateL', 'rotateR', 'shiftL', 'shiftR'

   * Bitwise logical ops: '.&.', '.|.', 'xor', 'complement'

   * Extraction and concatenation: 'bvExtract', '#', 'zeroExtend', 'signExtend', 'bvDrop', and 'bvTake'

Usual arithmetic ('Prelude.+', 'Prelude.-', '*', 'sQuotRem', 'sQuot', 'sRem', 'sDivMod', 'sDiv', 'sMod') and logical operations ('.<', '.<=', '.>', '.>=', '.==', './=') operations are
supported for 'SInteger' fully, both in programming and verification modes.
-}

{- $algReals
Algebraic reals are roots of single-variable polynomials with rational coefficients. (See
<http://en.wikipedia.org/wiki/Algebraic_number>.) Note that algebraic reals are infinite
precision numbers, but they do not cover all /real/ numbers. (In particular, they cannot
represent transcendentals.) Some irrational numbers are algebraic (such as @sqrt 2@), while
others are not (such as pi and e).

SBV can deal with real numbers just fine, since the theory of reals is decidable. (See
<http://smtlib.cs.uiowa.edu/theories-Reals.shtml>.) In addition, by leveraging backend
solver capabilities, SBV can also represent and solve non-linear equations involving real-variables.
(For instance, the Z3 SMT solver, supports polynomial constraints on reals starting with v4.0.)
-}

{- $floatingPoints
Floating point numbers are defined by the IEEE-754 standard; and correspond to Haskell's
'Float' and 'Double' types. For SMT support with floating-point numbers, see the paper
by Rummer and Wahl: <http://www.philipp.ruemmer.org/publications/smt-fpa.pdf>.
-}

{- $strings
Support for characters, strings, and regular expressions (initial version contributed by Joel Burget)
adds support for QF_S logic, described here: <http://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml>

See "Data.SBV.Char", "Data.SBV.String", "Data.SBV.RegExp" for related functions.
-}

{- $lists
Support for symbolic lists (initial version contributed by Joel Burget) adds support for sequence support.

See "Data.SBV.List" for related functions.
-}

{- $tuples
Tuples can be used as symbolic values. This is useful in combination with lists, for example @SBV [(Integer, String)]@ is a valid type. These types can be arbitrarily nested, eg @SBV [(Integer, [(Char, (Integer, String))])]@. Instances of upto 8-tuples are provided.
-}

{- $shiftRotate
Symbolic words (both signed and unsigned) are an instance of Haskell's 'Bits' class, so regular
bitwise operations are automatically available for them. Shifts and rotates, however, require
specialized type-signatures since Haskell insists on an 'Int' second argument for them.
-}

{- $partitionIntro
The function 'partition' allows one to restrict the results returned by calls to 'Data.SBV.allSat'.
In certain cases, we might consider certain models to be "equivalent," i.e., we might want to
create equivalence classes over the search space when it comes to what we consider all satisfying
solutions. In these cases, we can use 'partition' to tell SBV what classes of solutions to consider
as unique. Consider:

>>> :{
allSat $ do
   x <- sInteger "x"
   y <- sInteger "y"
   partition "p1" $ x .>= 0
   partition "p2" $ y .>= 0
:}
Solution #1:
  x  =     0 :: Integer
  y  =    -1 :: Integer
  p1 =  True :: Bool
  p2 = False :: Bool
Solution #2:
  x  =    -1 :: Integer
  y  =     0 :: Integer
  p1 = False :: Bool
  p2 =  True :: Bool
Solution #3:
  x  =    -1 :: Integer
  y  =    -1 :: Integer
  p1 = False :: Bool
  p2 = False :: Bool
Solution #4:
  x  =    0 :: Integer
  y  =    0 :: Integer
  p1 = True :: Bool
  p2 = True :: Bool
Found 4 different solutions.

Without the call to 'partition' in the above example, 'allSat' would return all possible combinations of @x@ and @y@ subject to the constraints. (Since we have none here,
the call would try to enumerate the infinite set of all integer tuples!) But 'partition' allows us to restrict our attention to the examples that satisfy the partitioning
constraints. The first argument to 'partition' is simply a name, for diagnostic purposes. Note that the conditions given by 'partition' are /not/ imposed on the search
space at all: They're only used when we construct the search space. In the above example, we pick one example from each quadrant. Furthermore, while it is typical to pass
a boolean as a partitioning argument, it is not required: Any expression is OK, whose value creates the equivalence class:

>>> :{
allSat $ do
   x <- sInteger "x"
   partition "p" $ x `sMod` 3
:}
Solution #1:
  x = 2 :: Integer
  p = 2 :: Integer
Solution #2:
  x = 1 :: Integer
  p = 1 :: Integer
Solution #3:
  x = 0 :: Integer
  p = 0 :: Integer
Found 3 different solutions.

In the above, we get three examples, as the expression @x mod 3@ can take only three different values.
-}

{- $constrainIntro
A constraint is a means for restricting the input domain of a formula. Here's a simple
example:

@
   do x <- 'free' \"x\"
      y <- 'free' \"y\"
      'constrain' $ x .> y
      'constrain' $ x + y .>= 12
      'constrain' $ y .>= 3
      ...
@

The first constraint requires @x@ to be larger than @y@. The scond one says that
sum of @x@ and @y@ must be at least @12@, and the final one says that @y@ to be at least @3@.
Constraints provide an easy way to assert additional properties on the input domain, right at the point of
the introduction of variables.

Note that the proper reading of a constraint
depends on the context:

  * In a 'sat' (or 'allSat') call: The constraint added is asserted
    conjunctively. That is, the resulting satisfying model (if any) will
    always satisfy all the constraints given.

  * In a 'prove' call: In this case, the constraint acts as an implication.
    The property is proved under the assumption that the constraint
    holds. In other words, the constraint says that we only care about
    the input space that satisfies the constraint.

  * In a @quickCheck@ call: The constraint acts as a filter for @quickCheck@;
    if the constraint does not hold, then the input value is considered to be irrelevant
    and is skipped. Note that this is similar to 'prove', but is stronger: We do not
    accept a test case to be valid just because the constraints fail on them, although
    semantically the implication does hold. We simply skip that test case as a /bad/
    test vector.

  * In a 'Data.SBV.Tools.GenTest.genTest' call: Similar to @quickCheck@ and 'prove': If a constraint
    does not hold, the input value is ignored and is not included in the test
    set.
-}

{- $generalConstraints
A good use case (in fact the motivating use case) for 'constrain' is attaching a
constraint to a variable at the time of its creation.
Also, the conjunctive semantics for 'sat' and the implicative
semantics for 'prove' simplify programming by choosing the correct interpretation
automatically. However, one should be aware of the semantic difference. For instance, in
the presence of constraints, formulas that are /provable/ are not necessarily
/satisfiable/. To wit, consider:

 @
    do x <- 'free' \"x\"
       'constrain' $ x .< x
       return $ x .< (x :: 'SWord8')
 @

This predicate is unsatisfiable since no element of 'SWord8' is less than itself. But
it's (vacuously) true, since it excludes the entire domain of values, thus making the proof
trivial. Hence, this predicate is provable, but is not satisfiable. To make sure the given
constraints are not vacuous, the functions 'isVacuousProof' (and 'isVacuousProofWith') can be used.

Also note that this semantics imply that test case generation ('Data.SBV.Tools.GenTest.genTest') and
quick-check can take arbitrarily long in the presence of constraints, if the random input values generated
rarely satisfy the constraints. (As an extreme case, consider @'constrain' 'sFalse'@.)
-}

{- $quantifiers
You can write quantified formulas, and reason with them as in first-order logic. Here is a simple example:

@
    constrain $ \\(Forall x) (Exists y) -> y .> (x :: SInteger)
@

You can nest quantifiers as you wish, and the quantified parameters can be of arbitrary symbolic type.
Additionally, you can convert such a quantified formula to a regular boolean, via a call to 'quantifiedBool'
function, essentially performing quantifier elimination:

@
    other_condition .&& quantifiedBool (\\(Forall x) (Exists y) -> y .> (x :: SInteger))
@

Or you can prove/sat quantified formulas directly:

@
    prove $ \\(Forall x) (Exists y) -> y .> (x :: SInteger)
@

This facility makes quantifiers part of the regular SBV language, allowing them to be mixed/matched with all
your other symbolic computations.  See the following files demonstrating reasoning with quantifiers:

   * "Documentation.SBV.Examples.Puzzles.Birthday"
   * "Documentation.SBV.Examples.Puzzles.KnightsAndKnaves"
   * "Documentation.SBV.Examples.Puzzles.Rabbits"
   * "Documentation.SBV.Examples.Misc.FirstOrderLogic"

SBV also supports the constructors 'ExistsUnique' to create unique existentials, in addition to
'ForallN' and 'ExistsN' for creating multiple variables at the same time.

In general, SBV will not display the values of quantified variables for a satisfying instance.
For a satisfiability problem, you can apply skolemization manually to have these values
computed by the backend solver. Note that skolemization will produce functions for
existentials under universals, and SBV generally cannot translate function values back
to Haskell, except in certain simple cases. However, for prefix existentials, the manual
transformation can pay off. As an example, compare:

>>> sat $ \(Exists x) (Forall y) -> x .<= (y :: SWord8)
Satisfiable

to:

>>> sat $ do { x <- free "x"; pure (quantifiedBool (\(Forall y) -> x .<= (y :: SWord8))) }
Satisfiable. Model:
  x = 0 :: Word8

where we have skolemized the top-level existential out, and received a witness value for it.
-}

{- $constraintVacuity

When adding constraints, one has to be careful about
making sure they are not inconsistent. The function 'isVacuousProof' can be used for this purpose.
Here is an example. Consider the following predicate:

    >>> let pred = do { x <- free "x"; constrain $ x .< x; return $ x .>= (5 :: SWord8) }

This predicate asserts that all 8-bit values are larger than 5, subject to the constraint that the
values considered satisfy @x .< x@, i.e., they are less than themselves. Since there are no values that
satisfy this constraint, the proof will pass vacuously:

    >>> prove pred
    Q.E.D.

We can use 'isVacuousProof' to make sure to see that the pass was vacuous:

    >>> isVacuousProof pred
    True

While the above example is trivial, things can get complicated if there are multiple constraints with
non-straightforward relations; so if constraints are used one should make sure to check the predicate
is not vacuously true. Here's an example that is not vacuous:

     >>> let pred' = do { x <- free "x"; constrain $ x .> 6; return $ x .>= (5 :: SWord8) }

This time the proof passes as expected:

     >>> prove pred'
     Q.E.D.

And the proof is not vacuous:

     >>> isVacuousProof pred'
     False
-}

{- $namedConstraints

Constraints can be given names:

  @ 'namedConstraint' "a is at least 5" $ a .>= 5@

Similarly, arbitrary term attributes can also be associated:

  @ 'constrainWithAttribute' [(":solver-specific-attribute", "value")] $ a .>= 5@

Note that a 'namedConstraint' is equivalent to a 'constrainWithAttribute' call, setting the `":named"' attribute.
-}

{- $unsatCores
Named constraints are useful when used in conjunction with 'Data.SBV.Control.getUnsatCore' function
where the backend solver can be queried to obtain an unsat core in case the constraints are unsatisfiable.
See 'Data.SBV.Control.getUnsatCore' for details and "Documentation.SBV.Examples.Queries.UnsatCore" for an example use case.
-}

{- $uninterpreted
Users can introduce new uninterpreted sorts simply by defining an empty data-type in Haskell and registering it as such. The
following example demonstrates:

  @
     data B
     mkUninterpretedSort ''B
  @

(Note that you'll also need to use pragmas @TemplateHaskell@, @StandAloneDeriving@, @DeriveDataTypeable@, and @DeriveAnyClass@ for this to work, follow GHC's error messages!)

This is all it takes to introduce @B@ as an uninterpreted sort in SBV, which makes the type @SBV B@ automagically become available as the type
of symbolic values that ranges over @B@ values. Note that this will also introduce the type @SB@ into your environment, which is a synonym
for @SBV B@.


Uninterpreted functions over both uninterpreted and regular sorts can be declared using the facilities introduced by
the 'Data.SBV.Core.Model.SMTDefinable' class.
-}

{- $enumerations
If the uninterpreted sort definition takes the form of an enumeration (i.e., a simple data type with all nullary constructors), then
you can use the 'mkSymbolicEnumeration' function to turn it into an enumeration in SMTLib.
A simple example is:

@
    data X = A | B | C
    mkSymbolicEnumeration ''X
@

Note the magic incantation @mkSymbolicEnumeration ''X@. For this to work, you need to have the following
options turned on:

>   LANGUAGE TemplateHaskell
>   LANGUAGE StandaloneDeriving
>   LANGUAGE DeriveDataTypeable
>   LANGUAGE DeriveAnyClass

The declaration will automatically introduce the type:

@
    type SX = SBV X
@

along with symbolic values of each of the enumerated values @sA@, @sB@, and @sC@. This way,
you can refer to the symbolic version as @SX@, treating it as a regular symbolic type ranging over the values @A@, @B@, and @C@. Such values can be compared for equality, and with the usual
other comparison operators, such as @.==@, @./=@, @.>@, @.>=@, @<@, and @<=@. For each enumerated value @X@, the symbolic versions @sX@ is defined to be equal to @literal X@.

A simple query would look like:

@
     allSat $ \x -> x .== (x :: SX)
@

which would list all three elements of this domain as satisfying solutions.

@
     Solution #1:
       s0 = A :: X
     Solution #2:
       s0 = B :: X
     Solution #3:
       s0 = C :: X
     Found 3 different solutions.
@

Note that the result is properly typed as @X@ elements; these are not mere strings.

See "Documentation.SBV.Examples.Misc.Enumerate" for an extended example on how to use symbolic enumerations.
-}

{- $cardIntro
A pseudo-boolean function (<http://en.wikipedia.org/wiki/Pseudo-Boolean_function>) is a
function from booleans to reals, basically treating 'True' as @1@ and 'False' as @0@. They
are typically expressed in polynomial form. Such functions can be used to express cardinality
constraints, where we want to /count/ how many things satisfy a certain condition.

One can code such constraints using regular SBV programming: Simply
walk over the booleans and the corresponding coefficients, and assert the required relation.
For instance:

   > [b0, b1, b2, b3] `pbAtMost` 2

is precisely equivalent to:

   > sum (map (\b -> ite b 1 0) [b0, b1, b2, b3]) .<= 2

and they both express that at most /two/ of @b0@, @b1@, @b2@, and @b3@ can be 'sTrue'.
However, the equivalent forms give rise to long formulas and the cardinality constraint
can get lost in the translation. The idea here is that if you use these functions instead, SBV will
produce better translations to SMTLib for more efficient solving of cardinality constraints, assuming
the backend solver supports them. Currently, only Z3 supports pseudo-booleans directly. For all other solvers,
SBV will translate these to equivalent terms that do not require special functions.
-}

{- $verbosity

SBV provides various levels of verbosity to aid in debugging, by using the 'SMTConfig' fields:

  * ['verbose'] Print on stdout a shortened account of what is sent/received. This is specifically trimmed to reduce noise
    and is good for quick debugging. The output is not supposed to be machine-readable.
  * ['redirectVerbose'] Send the verbose output to a file. Note that you still have to set `verbose=True` for redirection to
    take effect. Otherwise, the output is the same as what you would see in `verbose`.
  * ['transcript'] Produce a file that is valid SMTLib2 format, containing everything sent and received. In particular, one can
    directly feed this file to the SMT-solver outside of the SBV since it is machine-readable. This is good for offline analysis
    situations, where you want to have a full account of what happened. For instance, it will print time-stamps at every interaction
    point, so you can see how long each command took.
-}

{- $observeInternal

The 'observe' command can be used to trace values of arbitrary expressions during a 'sat', 'prove', or perhaps more
importantly, in a @quickCheck@ call with the 'sObserve' variant.. This is useful for, for instance, recording expected vs. obtained expressions
as a symbolic program is executing.

>>> :{
prove $ do a1 <- free "i1"
           a2 <- free "i2"
           let spec, res :: SWord8
               spec = a1 + a2
               res  = ite (a1 .== 12 .&& a2 .== 22)   -- insert a malicious bug!
                          1
                          (a1 + a2)
           return $ observe "Expected" spec .== observe "Result" res
:}
Falsifiable. Counter-example:
  Expected = 34 :: Word8
  Result   =  1 :: Word8
  i1       = 12 :: Word8
  i2       = 22 :: Word8

The 'observeIf' variant allows the user to specify a boolean condition when the value is interesting to observe. Useful when
you have lots of "debugging" points, but not all are of interest. Use the 'sObserve' variant when you are at the 'Symbolic'
monad, which also supports quick-check applications.
-}

{- $distinctNote
Symbolic equality provides the notion of what it means to be equal, similar to Haskell's 'Eq' class, except allowing comparison of
symbolic values. The methods are '.==' and './=', returning 'SBool' results. We also provide a notion of strong equality ('.===' and './=='),
which is useful for floating-point value comparisons as it deals more uniformly with @NaN@ and positive/negative zeros. Additionally, we
provide 'distinct' that can be used to assert all elements of a list are different from each other, and 'distinctExcept' which is similar
to 'distinct' but allows for certain values to be considered different. These latter two functions are useful in modeling a variety of
puzzles and cardinality constraints:

>>> prove $ \a -> distinctExcept [a, a] [0::SInteger] .<=> a .== 0
Q.E.D.
>>> prove $ \a b -> distinctExcept [a, b] [0::SWord8] .<=> (a .== b .=> a .== 0)
Q.E.D.
>>> prove $ \a b c d -> distinctExcept [a, b, c, d] [] .== distinct [a, b, c, (d::SInteger)]
Q.E.D.
-}

{- $euclidianNote
=== Euclidian division and modulus

Euclidian division and modulus for integers differ from regular division modulus when
the divisor is negative. It satisfies the following desirable property: For any @m@, @n@, we have:

@
  Given @m@, @n@, s.t., n /= 0
  Let (q, r) = m `sEDivMod` n
  Then: m = n * q + r
   and 0 <= r <= |n| - 1
@

That is, the modulus is always positive.
There's no standard Haskell function that performs this operation. The main reason to prefer this
function is that SMT solvers can deal with them better.
Compare:

>>> sDivMod @SInteger 3 (-2)
(-2 :: SInteger,-1 :: SInteger)
>>> sEDivMod 3 (-2)
(-1 :: SInteger,1 :: SInteger)
>>> prove $ \x y -> y .> 0 .=> x `sDivMod` y .== x `sEDivMod` y
Q.E.D.
-}

{- $conversionNote
Capture convertability from/to FloatingPoint representations.

Conversions to float: 'toSFloat' and 'toSDouble' simply return the
nearest representable float from the given type based on the rounding
mode provided. Similarly, 'toSFloatingPoint' converts to a generalized
floating-point number with specified exponent and significand bith widths.

Conversions from float: 'fromSFloat', 'fromSDouble', 'fromSFloatingPoint' functions do
the reverse conversion. However some care is needed when given values
that are not representable in the integral target domain. For instance,
converting an 'SFloat' to an 'SInt8' is problematic. The rules are as follows:

If the input value is a finite point and when rounded in the given rounding mode to an
integral value lies within the target bounds, then that result is returned.
(This is the regular interpretation of rounding in IEEE754.)

Otherwise (i.e., if the integral value in the float or double domain) doesn't
fit into the target type, then the result is unspecified. Note that if the input
is @+oo@, @-oo@, or @NaN@, then the result is unspecified.

Due to the unspecified nature of conversions, SBV will never constant fold
conversions from floats to integral values. That is, you will always get a
symbolic value as output. (Conversions from floats to other floats will be
constant folded. Conversions from integral values to floats will also be
constant folded.)

Note that unspecified really means unspecified: In particular, SBV makes
no guarantees about matching the behavior between what you might get in
Haskell, via SMT-Lib, or the C-translation. If the input value is out-of-bounds
as defined above, or is @NaN@ or @oo@ or @-oo@, then all bets are off. In particular
C and SMTLib are decidedly undefine this case, though that doesn't mean they do the
same thing! Same goes for Haskell, which seems to convert via Int64, but we do
not model that behavior in SBV as it doesn't seem to be intentional nor well documented.

You can check for @NaN@, @oo@ and @-oo@, using the predicates 'fpIsNaN', 'fpIsInfinite',
and 'fpIsPositive', 'fpIsNegative' predicates, respectively; and do the proper conversion
based on your needs. (0 is a good choice, as are min/max bounds of the target type.)

Currently, SBV provides no predicates to check if a value would lie within range for a
particular conversion task, as this depends on the rounding mode and the types involved
and can be rather tricky to determine. (See <http://github.com/LeventErkok/sbv/issues/456>
for a discussion of the issues involved.) In a future release, we hope to be able to
provide underflow and overflow predicates for these conversions as well.

Some examples to illustrate the behavior follows:

>>> :{
roundTrip :: forall a. (Eq a, IEEEFloatConvertible a) => SRoundingMode -> SBV a -> SBool
roundTrip m x = fromSFloat m (toSFloat m x) .== x
:}

>>> prove $ roundTrip @Int8
Q.E.D.
>>> prove $ roundTrip @Word8
Q.E.D.
>>> prove $ roundTrip @Int16
Q.E.D.
>>> prove $ roundTrip @Word16
Q.E.D.
>>> prove $ roundTrip @Int32
Falsifiable. Counter-example:
  s0 = RoundTowardNegative :: RoundingMode
  s1 =          -536873931 :: Int32

Note how we get a failure on `Int32`. The counter-example value is not representable exactly as a single precision float:

>>> toRational (-536873931 :: Float)
(-536873920) % 1

Note how the numerator is different, it is off by 11. This is hardly surprising, since floats become sparser as
the magnitude increases to be able to cover all the integer values representable.

>>> :{
roundTrip :: forall a. (Eq a, IEEEFloatConvertible a) => SRoundingMode -> SBV a -> SBool
roundTrip m x = fromSDouble m (toSDouble m x) .== x
:}

>>> prove $ roundTrip @Int8
Q.E.D.
>>> prove $ roundTrip @Word8
Q.E.D.
>>> prove $ roundTrip @Int16
Q.E.D.
>>> prove $ roundTrip @Word16
Q.E.D.
>>> prove $ roundTrip @Int32
Q.E.D.
>>> prove $ roundTrip @Word32
Q.E.D.
>>> prove $ roundTrip @Int64
Falsifiable. Counter-example:
  s0 = RoundNearestTiesToEven :: RoundingMode
  s1 =   -9223372036854775538 :: Int64

Just like in the `SFloat` case, once we reach 64-bits, we no longer can exactly represent the
integer value for all possible values:

>>> toRational (fromIntegral (-9223372036854775538 :: Int64) :: Double)
(-9223372036854775808) % 1

In this case the numerator is off by 270.
-}

-- | An implementation of rotate-left, using a barrel shifter like design. Only works when both
-- arguments are finite bitvectors, and furthermore when the second argument is unsigned.
-- The first condition is enforced by the type, but the second is dynamically checked.
-- We provide this implementation as an alternative to `sRotateLeft` since SMTLib logic
-- does not support variable argument rotates (as opposed to shifts), and thus this
-- implementation can produce better code for verification compared to `sRotateLeft`.
--
-- >>> prove $ \x y -> (x `sBarrelRotateLeft`  y) `sBarrelRotateRight` (y :: SWord32) .== (x :: SWord64)
-- Q.E.D.
sBarrelRotateLeft :: (SFiniteBits a, SFiniteBits b) => SBV a -> SBV b -> SBV a
sBarrelRotateLeft = M.sBarrelRotateLeft

-- | An implementation of rotate-right, using a barrel shifter like design. See comments
-- for `sBarrelRotateLeft` for details.
--
-- >>> prove $ \x y -> (x `sBarrelRotateRight` y) `sBarrelRotateLeft`  (y :: SWord32) .== (x :: SWord64)
-- Q.E.D.
sBarrelRotateRight :: (SFiniteBits a, SFiniteBits b) => SBV a -> SBV b -> SBV a
sBarrelRotateRight = M.sBarrelRotateRight

-- | Extract a portion of bits to form a smaller bit-vector.
--
-- >>> prove $ \x -> bvExtract (Proxy @7) (Proxy @3) (x :: SWord 12) .== bvDrop (Proxy @4) (bvTake (Proxy @9) x)
-- Q.E.D.
bvExtract :: forall i j n bv proxy. ( KnownNat n, BVIsNonZero n, SymVal (bv n)
                                    , KnownNat i
                                    , KnownNat j
                                    , i + 1 <= n
                                    , j <= i
                                    , BVIsNonZero (i - j + 1)
                                    ) => proxy i                -- ^ @i@: Start position, numbered from @n-1@ to @0@
                                      -> proxy j                -- ^ @j@: End position, numbered from @n-1@ to @0@, @j <= i@ must hold
                                      -> SBV (bv n)             -- ^ Input bit vector of size @n@
                                      -> SBV (bv (i - j + 1))   -- ^ Output is of size @i - j + 1@
bvExtract = CS.bvExtract

-- | Join two bitvectors.
--
-- >>> prove $ \x y -> x .== bvExtract (Proxy @79) (Proxy @71) ((x :: SWord 9) # (y :: SWord 71))
-- Q.E.D.
(#) :: ( KnownNat n, BVIsNonZero n, SymVal (bv n)
       , KnownNat m, BVIsNonZero m, SymVal (bv m)
       ) => SBV (bv n)                     -- ^ First input, of size @n@, becomes the left side
         -> SBV (bv m)                     -- ^ Second input, of size @m@, becomes the right side
         -> SBV (bv (n + m))               -- ^ Concatenation, of size @n+m@
(#) = (CS.#)
infixr 5 #

-- | Zero extend a bit-vector.
--
-- >>> prove $ \x -> bvExtract (Proxy @20) (Proxy @12) (zeroExtend (x :: SInt 12) :: SInt 21) .== 0
-- Q.E.D.
zeroExtend :: forall n m bv. ( KnownNat n, BVIsNonZero n, SymVal (bv n)
                             , KnownNat m, BVIsNonZero m, SymVal (bv m)
                             , n + 1 <= m
                             , SIntegral (bv (m - n))
                             , BVIsNonZero (m - n)
                             ) => SBV (bv n)    -- ^ Input, of size @n@
                               -> SBV (bv m)    -- ^ Output, of size @m@. @n < m@ must hold
zeroExtend = CS.zeroExtend

-- | Sign extend a bit-vector.
--
-- >>> prove $ \x -> sNot (msb x) .=> bvExtract (Proxy @20) (Proxy @12) (signExtend (x :: SInt 12) :: SInt 21) .== 0
-- Q.E.D.
-- >>> prove $ \x ->       msb x  .=> bvExtract (Proxy @20) (Proxy @12) (signExtend (x :: SInt 12) :: SInt 21) .== complement 0
-- Q.E.D.
signExtend :: forall n m bv. ( KnownNat n, BVIsNonZero n, SymVal (bv n)
                             , KnownNat m, BVIsNonZero m, SymVal (bv m)
                             , n + 1 <= m
                             , SFiniteBits (bv n)
                             , SIntegral   (bv (m - n))
                             , BVIsNonZero   (m - n)
                             ) => SBV (bv n)  -- ^ Input, of size @n@
                               -> SBV (bv m)  -- ^ Output, of size @m@. @n < m@ must hold
signExtend = CS.signExtend

-- | Drop bits from the top of a bit-vector.
--
-- >>> prove $ \x -> bvDrop (Proxy @0) (x :: SWord 43) .== x
-- Q.E.D.
-- >>> prove $ \x -> bvDrop (Proxy @20) (x :: SWord 21) .== ite (lsb x) 1 (0 :: SWord 1)
-- Q.E.D.
bvDrop :: forall i n m bv proxy. ( KnownNat n, BVIsNonZero n
                                 , KnownNat i
                                 , i + 1 <= n
                                 , i + m - n <= 0
                                 , BVIsNonZero (n - i)
                                 ) => proxy i                    -- ^ @i@: Number of bits to drop. @i < n@ must hold.
                                   -> SBV (bv n)                 -- ^ Input, of size @n@
                                   -> SBV (bv m)                 -- ^ Output, of size @m@. @m = n - i@ holds.
bvDrop = CS.bvDrop

-- | Take bits from the top of a bit-vector.
--
-- >>> prove $ \x -> bvTake (Proxy @13) (x :: SWord 13) .== x
-- Q.E.D.
-- >>> prove $ \x -> bvTake (Proxy @1) (x :: SWord 13) .== ite (msb x) 1 0
-- Q.E.D.
-- >>> prove $ \x -> bvTake (Proxy @4) x # bvDrop (Proxy @4) x .== (x :: SWord 23)
-- Q.E.D.
bvTake :: forall i n bv proxy. ( KnownNat n, BVIsNonZero n
                               , KnownNat i, BVIsNonZero i
                               , i <= n
                               ) => proxy i                  -- ^ @i@: Number of bits to take. @0 < i <= n@ must hold.
                                 -> SBV (bv n)               -- ^ Input, of size @n@
                                 -> SBV (bv i)               -- ^ Output, of size @i@
bvTake = CS.bvTake

-- | A helper class to convert sized bit-vectors to/from bytes.
class ByteConverter a where
   -- | Convert to a sequence of bytes
   --
   -- >>> prove $ \a b c d -> toBytes ((fromBytes [a, b, c, d]) :: SWord 32) .== [a, b, c, d]
   -- Q.E.D.
   toBytes   :: a -> [SWord 8]

   -- | Convert from a sequence of bytes
   --
   -- >>> prove $ \r -> fromBytes (toBytes r) .== (r :: SWord 64)
   -- Q.E.D.
   fromBytes :: [SWord 8] -> a

-- NB. The following instances are automatically generated by buildUtils/genByteConverter.hs
-- It is possible to write these more compactly indeed, but this explicit form generates
-- better C code, and hence we allow the verbosity here.

-- | 'SWord' 8 instance for 'ByteConverter'
instance ByteConverter (SWord 8) where
   toBytes a = [a]

   fromBytes [x] = x
   fromBytes as  = error $ "fromBytes:SWord 8: Incorrect number of bytes: " ++ show (length as)

-- | 'SWord' 16 instance for 'ByteConverter'
instance ByteConverter (SWord 16) where
   toBytes a = [ bvExtract (Proxy @15) (Proxy  @8) a
               , bvExtract (Proxy  @7) (Proxy  @0) a
               ]

   fromBytes as
     | l == 2
     = (fromBytes :: [SWord 8] -> SWord 8) (take 1 as) # fromBytes (drop 1 as)
     | True
     = error $ "fromBytes:SWord 16: Incorrect number of bytes: " ++ show l
     where l = length as

-- | 'SWord' 32 instance for 'ByteConverter'
instance ByteConverter (SWord 32) where
   toBytes a = [ bvExtract (Proxy @31) (Proxy @24) a, bvExtract (Proxy @23) (Proxy @16) a, bvExtract (Proxy @15) (Proxy  @8) a, bvExtract (Proxy  @7) (Proxy  @0) a
               ]

   fromBytes as
     | l == 4
     = (fromBytes :: [SWord 8] -> SWord 16) (take 2 as) # fromBytes (drop 2 as)
     | True
     = error $ "fromBytes:SWord 32: Incorrect number of bytes: " ++ show l
     where l = length as

-- | 'SWord' 64 instance for 'ByteConverter'
instance ByteConverter (SWord 64) where
   toBytes a = [ bvExtract (Proxy @63) (Proxy @56) a, bvExtract (Proxy @55) (Proxy @48) a, bvExtract (Proxy @47) (Proxy @40) a, bvExtract (Proxy @39) (Proxy @32) a
               , bvExtract (Proxy @31) (Proxy @24) a, bvExtract (Proxy @23) (Proxy @16) a, bvExtract (Proxy @15) (Proxy  @8) a, bvExtract (Proxy  @7) (Proxy  @0) a
               ]

   fromBytes as
     | l == 8
     = (fromBytes :: [SWord 8] -> SWord 32) (take 4 as) # fromBytes (drop 4 as)
     | True
     = error $ "fromBytes:SWord 64: Incorrect number of bytes: " ++ show l
     where l = length as

-- | 'SWord' 128 instance for 'ByteConverter'
instance ByteConverter (SWord 128) where
   toBytes a = [ bvExtract (Proxy @127) (Proxy @120) a, bvExtract (Proxy @119) (Proxy @112) a, bvExtract (Proxy @111) (Proxy @104) a, bvExtract (Proxy @103) (Proxy  @96) a
               , bvExtract (Proxy  @95) (Proxy  @88) a, bvExtract (Proxy  @87) (Proxy  @80) a, bvExtract (Proxy  @79) (Proxy  @72) a, bvExtract (Proxy  @71) (Proxy  @64) a
               , bvExtract (Proxy  @63) (Proxy  @56) a, bvExtract (Proxy  @55) (Proxy  @48) a, bvExtract (Proxy  @47) (Proxy  @40) a, bvExtract (Proxy  @39) (Proxy  @32) a
               , bvExtract (Proxy  @31) (Proxy  @24) a, bvExtract (Proxy  @23) (Proxy  @16) a, bvExtract (Proxy  @15) (Proxy   @8) a, bvExtract (Proxy   @7) (Proxy   @0) a
               ]

   fromBytes as
     | l == 16
     = (fromBytes :: [SWord 8] -> SWord 64) (take 8 as) # fromBytes (drop 8 as)
     | True
     = error $ "fromBytes:SWord 128: Incorrect number of bytes: " ++ show l
     where l = length as

-- | 'SWord' 256 instance for 'ByteConverter'
instance ByteConverter (SWord 256) where
   toBytes a = [ bvExtract (Proxy @255) (Proxy @248) a, bvExtract (Proxy @247) (Proxy @240) a, bvExtract (Proxy @239) (Proxy @232) a, bvExtract (Proxy @231) (Proxy @224) a
               , bvExtract (Proxy @223) (Proxy @216) a, bvExtract (Proxy @215) (Proxy @208) a, bvExtract (Proxy @207) (Proxy @200) a, bvExtract (Proxy @199) (Proxy @192) a
               , bvExtract (Proxy @191) (Proxy @184) a, bvExtract (Proxy @183) (Proxy @176) a, bvExtract (Proxy @175) (Proxy @168) a, bvExtract (Proxy @167) (Proxy @160) a
               , bvExtract (Proxy @159) (Proxy @152) a, bvExtract (Proxy @151) (Proxy @144) a, bvExtract (Proxy @143) (Proxy @136) a, bvExtract (Proxy @135) (Proxy @128) a
               , bvExtract (Proxy @127) (Proxy @120) a, bvExtract (Proxy @119) (Proxy @112) a, bvExtract (Proxy @111) (Proxy @104) a, bvExtract (Proxy @103) (Proxy  @96) a
               , bvExtract (Proxy  @95) (Proxy  @88) a, bvExtract (Proxy  @87) (Proxy  @80) a, bvExtract (Proxy  @79) (Proxy  @72) a, bvExtract (Proxy  @71) (Proxy  @64) a
               , bvExtract (Proxy  @63) (Proxy  @56) a, bvExtract (Proxy  @55) (Proxy  @48) a, bvExtract (Proxy  @47) (Proxy  @40) a, bvExtract (Proxy  @39) (Proxy  @32) a
               , bvExtract (Proxy  @31) (Proxy  @24) a, bvExtract (Proxy  @23) (Proxy  @16) a, bvExtract (Proxy  @15) (Proxy   @8) a, bvExtract (Proxy   @7) (Proxy   @0) a
               ]

   fromBytes as
     | l == 32
     = (fromBytes :: [SWord 8] -> SWord 128) (take 16 as) # fromBytes (drop 16 as)
     | True
     = error $ "fromBytes:SWord 256: Incorrect number of bytes: " ++ show l
     where l = length as

-- | 'SWord' 512 instance for 'ByteConverter'
instance ByteConverter (SWord 512) where
   toBytes a = [ bvExtract (Proxy @511) (Proxy @504) a, bvExtract (Proxy @503) (Proxy @496) a, bvExtract (Proxy @495) (Proxy @488) a, bvExtract (Proxy @487) (Proxy @480) a
               , bvExtract (Proxy @479) (Proxy @472) a, bvExtract (Proxy @471) (Proxy @464) a, bvExtract (Proxy @463) (Proxy @456) a, bvExtract (Proxy @455) (Proxy @448) a
               , bvExtract (Proxy @447) (Proxy @440) a, bvExtract (Proxy @439) (Proxy @432) a, bvExtract (Proxy @431) (Proxy @424) a, bvExtract (Proxy @423) (Proxy @416) a
               , bvExtract (Proxy @415) (Proxy @408) a, bvExtract (Proxy @407) (Proxy @400) a, bvExtract (Proxy @399) (Proxy @392) a, bvExtract (Proxy @391) (Proxy @384) a
               , bvExtract (Proxy @383) (Proxy @376) a, bvExtract (Proxy @375) (Proxy @368) a, bvExtract (Proxy @367) (Proxy @360) a, bvExtract (Proxy @359) (Proxy @352) a
               , bvExtract (Proxy @351) (Proxy @344) a, bvExtract (Proxy @343) (Proxy @336) a, bvExtract (Proxy @335) (Proxy @328) a, bvExtract (Proxy @327) (Proxy @320) a
               , bvExtract (Proxy @319) (Proxy @312) a, bvExtract (Proxy @311) (Proxy @304) a, bvExtract (Proxy @303) (Proxy @296) a, bvExtract (Proxy @295) (Proxy @288) a
               , bvExtract (Proxy @287) (Proxy @280) a, bvExtract (Proxy @279) (Proxy @272) a, bvExtract (Proxy @271) (Proxy @264) a, bvExtract (Proxy @263) (Proxy @256) a
               , bvExtract (Proxy @255) (Proxy @248) a, bvExtract (Proxy @247) (Proxy @240) a, bvExtract (Proxy @239) (Proxy @232) a, bvExtract (Proxy @231) (Proxy @224) a
               , bvExtract (Proxy @223) (Proxy @216) a, bvExtract (Proxy @215) (Proxy @208) a, bvExtract (Proxy @207) (Proxy @200) a, bvExtract (Proxy @199) (Proxy @192) a
               , bvExtract (Proxy @191) (Proxy @184) a, bvExtract (Proxy @183) (Proxy @176) a, bvExtract (Proxy @175) (Proxy @168) a, bvExtract (Proxy @167) (Proxy @160) a
               , bvExtract (Proxy @159) (Proxy @152) a, bvExtract (Proxy @151) (Proxy @144) a, bvExtract (Proxy @143) (Proxy @136) a, bvExtract (Proxy @135) (Proxy @128) a
               , bvExtract (Proxy @127) (Proxy @120) a, bvExtract (Proxy @119) (Proxy @112) a, bvExtract (Proxy @111) (Proxy @104) a, bvExtract (Proxy @103) (Proxy  @96) a
               , bvExtract (Proxy  @95) (Proxy  @88) a, bvExtract (Proxy  @87) (Proxy  @80) a, bvExtract (Proxy  @79) (Proxy  @72) a, bvExtract (Proxy  @71) (Proxy  @64) a
               , bvExtract (Proxy  @63) (Proxy  @56) a, bvExtract (Proxy  @55) (Proxy  @48) a, bvExtract (Proxy  @47) (Proxy  @40) a, bvExtract (Proxy  @39) (Proxy  @32) a
               , bvExtract (Proxy  @31) (Proxy  @24) a, bvExtract (Proxy  @23) (Proxy  @16) a, bvExtract (Proxy  @15) (Proxy   @8) a, bvExtract (Proxy   @7) (Proxy   @0) a
               ]

   fromBytes as
     | l == 64
     = (fromBytes :: [SWord 8] -> SWord 256) (take 32 as) # fromBytes (drop 32 as)
     | True
     = error $ "fromBytes:SWord 512: Incorrect number of bytes: " ++ show l
     where l = length as

-- | 'SWord' 1024 instance for 'ByteConverter'
instance ByteConverter (SWord 1024) where
   toBytes a = [ bvExtract (Proxy @1023) (Proxy @1016) a, bvExtract (Proxy @1015) (Proxy @1008) a, bvExtract (Proxy @1007) (Proxy @1000) a, bvExtract (Proxy  @999) (Proxy  @992) a
               , bvExtract (Proxy  @991) (Proxy  @984) a, bvExtract (Proxy  @983) (Proxy  @976) a, bvExtract (Proxy  @975) (Proxy  @968) a, bvExtract (Proxy  @967) (Proxy  @960) a
               , bvExtract (Proxy  @959) (Proxy  @952) a, bvExtract (Proxy  @951) (Proxy  @944) a, bvExtract (Proxy  @943) (Proxy  @936) a, bvExtract (Proxy  @935) (Proxy  @928) a
               , bvExtract (Proxy  @927) (Proxy  @920) a, bvExtract (Proxy  @919) (Proxy  @912) a, bvExtract (Proxy  @911) (Proxy  @904) a, bvExtract (Proxy  @903) (Proxy  @896) a
               , bvExtract (Proxy  @895) (Proxy  @888) a, bvExtract (Proxy  @887) (Proxy  @880) a, bvExtract (Proxy  @879) (Proxy  @872) a, bvExtract (Proxy  @871) (Proxy  @864) a
               , bvExtract (Proxy  @863) (Proxy  @856) a, bvExtract (Proxy  @855) (Proxy  @848) a, bvExtract (Proxy  @847) (Proxy  @840) a, bvExtract (Proxy  @839) (Proxy  @832) a
               , bvExtract (Proxy  @831) (Proxy  @824) a, bvExtract (Proxy  @823) (Proxy  @816) a, bvExtract (Proxy  @815) (Proxy  @808) a, bvExtract (Proxy  @807) (Proxy  @800) a
               , bvExtract (Proxy  @799) (Proxy  @792) a, bvExtract (Proxy  @791) (Proxy  @784) a, bvExtract (Proxy  @783) (Proxy  @776) a, bvExtract (Proxy  @775) (Proxy  @768) a
               , bvExtract (Proxy  @767) (Proxy  @760) a, bvExtract (Proxy  @759) (Proxy  @752) a, bvExtract (Proxy  @751) (Proxy  @744) a, bvExtract (Proxy  @743) (Proxy  @736) a
               , bvExtract (Proxy  @735) (Proxy  @728) a, bvExtract (Proxy  @727) (Proxy  @720) a, bvExtract (Proxy  @719) (Proxy  @712) a, bvExtract (Proxy  @711) (Proxy  @704) a
               , bvExtract (Proxy  @703) (Proxy  @696) a, bvExtract (Proxy  @695) (Proxy  @688) a, bvExtract (Proxy  @687) (Proxy  @680) a, bvExtract (Proxy  @679) (Proxy  @672) a
               , bvExtract (Proxy  @671) (Proxy  @664) a, bvExtract (Proxy  @663) (Proxy  @656) a, bvExtract (Proxy  @655) (Proxy  @648) a, bvExtract (Proxy  @647) (Proxy  @640) a
               , bvExtract (Proxy  @639) (Proxy  @632) a, bvExtract (Proxy  @631) (Proxy  @624) a, bvExtract (Proxy  @623) (Proxy  @616) a, bvExtract (Proxy  @615) (Proxy  @608) a
               , bvExtract (Proxy  @607) (Proxy  @600) a, bvExtract (Proxy  @599) (Proxy  @592) a, bvExtract (Proxy  @591) (Proxy  @584) a, bvExtract (Proxy  @583) (Proxy  @576) a
               , bvExtract (Proxy  @575) (Proxy  @568) a, bvExtract (Proxy  @567) (Proxy  @560) a, bvExtract (Proxy  @559) (Proxy  @552) a, bvExtract (Proxy  @551) (Proxy  @544) a
               , bvExtract (Proxy  @543) (Proxy  @536) a, bvExtract (Proxy  @535) (Proxy  @528) a, bvExtract (Proxy  @527) (Proxy  @520) a, bvExtract (Proxy  @519) (Proxy  @512) a
               , bvExtract (Proxy  @511) (Proxy  @504) a, bvExtract (Proxy  @503) (Proxy  @496) a, bvExtract (Proxy  @495) (Proxy  @488) a, bvExtract (Proxy  @487) (Proxy  @480) a
               , bvExtract (Proxy  @479) (Proxy  @472) a, bvExtract (Proxy  @471) (Proxy  @464) a, bvExtract (Proxy  @463) (Proxy  @456) a, bvExtract (Proxy  @455) (Proxy  @448) a
               , bvExtract (Proxy  @447) (Proxy  @440) a, bvExtract (Proxy  @439) (Proxy  @432) a, bvExtract (Proxy  @431) (Proxy  @424) a, bvExtract (Proxy  @423) (Proxy  @416) a
               , bvExtract (Proxy  @415) (Proxy  @408) a, bvExtract (Proxy  @407) (Proxy  @400) a, bvExtract (Proxy  @399) (Proxy  @392) a, bvExtract (Proxy  @391) (Proxy  @384) a
               , bvExtract (Proxy  @383) (Proxy  @376) a, bvExtract (Proxy  @375) (Proxy  @368) a, bvExtract (Proxy  @367) (Proxy  @360) a, bvExtract (Proxy  @359) (Proxy  @352) a
               , bvExtract (Proxy  @351) (Proxy  @344) a, bvExtract (Proxy  @343) (Proxy  @336) a, bvExtract (Proxy  @335) (Proxy  @328) a, bvExtract (Proxy  @327) (Proxy  @320) a
               , bvExtract (Proxy  @319) (Proxy  @312) a, bvExtract (Proxy  @311) (Proxy  @304) a, bvExtract (Proxy  @303) (Proxy  @296) a, bvExtract (Proxy  @295) (Proxy  @288) a
               , bvExtract (Proxy  @287) (Proxy  @280) a, bvExtract (Proxy  @279) (Proxy  @272) a, bvExtract (Proxy  @271) (Proxy  @264) a, bvExtract (Proxy  @263) (Proxy  @256) a
               , bvExtract (Proxy  @255) (Proxy  @248) a, bvExtract (Proxy  @247) (Proxy  @240) a, bvExtract (Proxy  @239) (Proxy  @232) a, bvExtract (Proxy  @231) (Proxy  @224) a
               , bvExtract (Proxy  @223) (Proxy  @216) a, bvExtract (Proxy  @215) (Proxy  @208) a, bvExtract (Proxy  @207) (Proxy  @200) a, bvExtract (Proxy  @199) (Proxy  @192) a
               , bvExtract (Proxy  @191) (Proxy  @184) a, bvExtract (Proxy  @183) (Proxy  @176) a, bvExtract (Proxy  @175) (Proxy  @168) a, bvExtract (Proxy  @167) (Proxy  @160) a
               , bvExtract (Proxy  @159) (Proxy  @152) a, bvExtract (Proxy  @151) (Proxy  @144) a, bvExtract (Proxy  @143) (Proxy  @136) a, bvExtract (Proxy  @135) (Proxy  @128) a
               , bvExtract (Proxy  @127) (Proxy  @120) a, bvExtract (Proxy  @119) (Proxy  @112) a, bvExtract (Proxy  @111) (Proxy  @104) a, bvExtract (Proxy  @103) (Proxy   @96) a
               , bvExtract (Proxy   @95) (Proxy   @88) a, bvExtract (Proxy   @87) (Proxy   @80) a, bvExtract (Proxy   @79) (Proxy   @72) a, bvExtract (Proxy   @71) (Proxy   @64) a
               , bvExtract (Proxy   @63) (Proxy   @56) a, bvExtract (Proxy   @55) (Proxy   @48) a, bvExtract (Proxy   @47) (Proxy   @40) a, bvExtract (Proxy   @39) (Proxy   @32) a
               , bvExtract (Proxy   @31) (Proxy   @24) a, bvExtract (Proxy   @23) (Proxy   @16) a, bvExtract (Proxy   @15) (Proxy    @8) a, bvExtract (Proxy    @7) (Proxy    @0) a
               ]

   fromBytes as
     | l == 128
     = (fromBytes :: [SWord 8] -> SWord 512) (take 64 as) # fromBytes (drop 64 as)
     | True
     = error $ "fromBytes:SWord 1024: Incorrect number of bytes: " ++ show l
     where l = length as

{- $specialRels
A special relation is a binary relation that has additional properties. SBV allows for the checking of various kinds
of special relations respecting various axioms, and allows for creating transitive closures.
See "Documentation.SBV.Examples.Misc.FirstOrderLogic" for several examples.
-}

-- | A type synonym for binary relations.
type Relation a = (SBV a, SBV a) -> SBool

-- | Check if a relation is a partial order. The string argument must uniquely identify this order.
isPartialOrder :: SymVal a => String -> Relation a -> SBool
isPartialOrder = checkSpecialRelation . IsPartialOrder

-- | Check if a relation is a linear order. The string argument must uniquely identify this order.
isLinearOrder :: SymVal a => String -> Relation a -> SBool
isLinearOrder = checkSpecialRelation . IsLinearOrder

-- | Check if a relation is a tree order. The string argument must uniquely identify this order.
isTreeOrder :: SymVal a => String -> Relation a -> SBool
isTreeOrder = checkSpecialRelation . IsTreeOrder

-- | Check if a relation is a piece-wise linear order. The string argument must uniquely identify this order.
isPiecewiseLinearOrder :: SymVal a => String -> Relation a -> SBool
isPiecewiseLinearOrder = checkSpecialRelation . IsPiecewiseLinearOrder

-- | Make sure it's internally acceptable
sanitizeRelName :: String -> String
sanitizeRelName s = "__internal_sbv_" ++ map sanitize s
  where sanitize c | isSpace c || isPunctuation c = '_'
                               | True             = c

-- | Create the transitive closure of a given relation. The string argument must uniquely identify the newly created relation.
mkTransitiveClosure :: forall a. SymVal a => String -> Relation a -> Relation a
mkTransitiveClosure nm rel = res
  where ka = kindOf (Proxy @a)

        -- The internal name of this relation
        inm = sanitizeRelName $ "_TransitiveClosure_" ++ nm ++ "_"
        key = (inm, nm)

        res (a, b) = SBV $ SVal KBool $ Right $ cache result
          where result st = do -- Is this new? If so create it, otherwise reuse
                               ProgInfo{progTransClosures = curProgTransClosures} <- readIORef (rProgInfo st)

                               when (key `notElem` curProgTransClosures) $ do

                                  registerKind st ka

                                  -- Add to the end so if we get incremental ones the order doesn't change for old ones!
                                  modifyIORef' (rProgInfo st) (\u -> u{progTransClosures = curProgTransClosures ++ [key]})

                                  -- Equate it to the relation we are given. We want to do this in the root state
                                  let SBV eq = quantifiedBool $ \(Forall x) (Forall y) -> rel (x, y) .== uninterpret inm x y
                                  internalConstraint (getRootState st) False [] eq

                               sa <- sbvToSV st a
                               sb <- sbvToSV st b

                               newExpr st KBool $ SBVApp (Uninterpreted nm) [sa, sb]

-- | Check if the given relation satisfies the required axioms
checkSpecialRelation :: forall a. SymVal a => SpecialRelOp -> Relation a -> SBool
checkSpecialRelation op rel = SBV $ SVal KBool $ Right $ cache result
  where ka = kindOf (Proxy @a)

        internalize nm = case op of
                           IsPartialOrder         _ -> IsPartialOrder         nm
                           IsLinearOrder          _ -> IsLinearOrder          nm
                           IsTreeOrder            _ -> IsTreeOrder            nm
                           IsPiecewiseLinearOrder _ -> IsPiecewiseLinearOrder nm

        result st = do -- The internal name of this relation
                       let nm  = sanitizeRelName (show op)
                           iop = internalize nm

                       -- Is this new? If so create it, otherwise reuse
                       ProgInfo{progSpecialRels = curSpecialRels} <- readIORef (rProgInfo st)

                       when (op `notElem` curSpecialRels) $ do

                          registerKind st ka
                          newUninterpreted st (nm, Nothing) (SBVType [ka, ka, KBool]) (UINone True)

                          -- Add to the end so if we get incremental ones the order doesn't change for old ones!
                          modifyIORef' (rProgInfo st) (\u -> u{progSpecialRels = curSpecialRels ++ [iop]})

                          -- Equate it to the relation we are given. We want to do this in the parent state
                          let SBV eq = quantifiedBool $ \(Forall x) (Forall y) -> rel (x, y) .== uninterpret nm x y
                          internalConstraint (getRootState st) False [] eq

                       newExpr st KBool $ SBVApp (SpecialRelOp ka iop) []

{- HLint ignore module "Use import/export shortcut" -}
