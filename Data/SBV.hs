---------------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
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
--   s0 = 32 :: Word8
--
-- The function 'prove' has the following type:
--
-- @
--     'prove' :: 'Provable' a => a -> 'IO' 'ThmResult'
-- @
--
-- The class 'Provable' comes with instances for n-ary predicates, for arbitrary n.
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
--   * 'SInteger': Unbounded signed integers.
--
--   * 'SReal': Algebraic-real numbers
--
--   * 'SFloat': IEEE-754 single-precision floating point values
--
--   * 'SDouble': IEEE-754 double-precision floating point values
--
--   * 'SArray', 'SFunArray': Flat arrays of symbolic values.
--
--   * Symbolic polynomials over GF(2^n), polynomial arithmetic, and CRCs.
--
--   * Uninterpreted constants and functions over symbolic values, with user
--     defined SMT-Lib axioms.
--
--   * Uninterpreted sorts, and proofs over such sorts, potentially with axioms.
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
--   * CVC4 from New York University and University of Iowa: <http://cvc4.cs.nyu.edu/>
--
--   * Boolector from Johannes Kepler University: <http://fmv.jku.at/boolector/>
--
--   * MathSAT from Fondazione Bruno Kessler and DISI-University of Trento: <http://mathsat.fbk.eu/>
--
--   * Yices from SRI: <http://yices.csl.sri.com/>
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
---------------------------------------------------------------------------------

{-# LANGUAGE    FlexibleInstances   #-}
{-# LANGUAGE    QuasiQuotes         #-}
{-# LANGUAGE    TemplateHaskell     #-}
{-# LANGUAGE    ScopedTypeVariables #-}
{-# LANGUAGE    StandaloneDeriving  #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

module Data.SBV (
  -- * Programming with symbolic values
  -- $progIntro

  -- ** Symbolic types

  -- *** Symbolic bit
    SBool
  -- *** Unsigned symbolic bit-vectors
  , SWord8, SWord16, SWord32, SWord64
  -- *** Signed symbolic bit-vectors
  , SInt8, SInt16, SInt32, SInt64
  -- *** Signed unbounded integers
  -- $unboundedLimitations
  , SInteger
  -- *** Floating point numbers
  -- $floatingPoints
  , SFloat, SDouble
  -- *** Signed algebraic reals
  -- $algReals
  , SReal, AlgReal, sRealToSInteger

  -- ** Creating a symbolic variable
  -- $createSym
  , sBool, sWord8, sWord16, sWord32, sWord64, sInt8, sInt16, sInt32, sInt64, sInteger, sReal, sFloat, sDouble

  -- ** Creating a list of symbolic variables
  -- $createSyms
  , sBools, sWord8s, sWord16s, sWord32s, sWord64s, sInt8s, sInt16s, sInt32s, sInt64s, sIntegers, sReals, sFloats, sDoubles

  -- *** Abstract SBV type
  , SBV, HasKind(..), Kind(..)
  -- *** Arrays of symbolic values
  , SymArray(..), SArray, SFunArray, mkSFunArray

  -- ** Operations on symbolic values
  -- *** Word level
  , sTestBit, sExtractBits, sPopCount, sShiftLeft, sShiftRight, sRotateLeft, sRotateRight, sSignedShiftArithRight, sFromIntegral, setBitTo, oneIf
  , lsb, msb, label

  -- *** Addition and Multiplication with high-bits
  , fullAdder, fullMultiplier
  -- *** Exponentiation
  , (.^)
  -- *** Blasting/Unblasting
  , blastBE, blastLE, FromBits(..)
  -- *** Splitting, joining, and extending
  , Splittable(..)

  -- ** Conditionals: Mergeable values
  , Mergeable(..), ite, iteLazy

  -- ** Symbolic integral numbers
  , SIntegral
  -- ** Division
  , SDivisible(..)
  -- ** The Boolean class
  , Boolean(..)
  -- *** Generalizations of boolean operations
  , bAnd, bOr, bAny, bAll

  -- * Uninterpreted sorts, constants, and functions
  -- $uninterpreted
  , Uninterpreted(..), addAxiom

  -- * Symbolic Equality and Comparisons
  , EqSymbolic(..), OrdSymbolic(..), Equality(..)

  -- * Constraints
  -- $constrainIntro
  , constrain, namedConstraint
  -- ** Cardinality constraints
  -- $cardIntro
  , pbAtMost, pbAtLeast, pbExactly, pbLe, pbGe, pbEq, pbMutexed, pbStronglyMutexed

  -- * Enumerations
  -- $enumerations
  , mkSymbolicEnumeration

  -- * Properties, proofs, satisfiability, and safety
  -- $proveIntro
  -- $noteOnNestedQuantifiers
  -- $multiIntro
  , Predicate, Goal, Provable(..)
  -- ** Checking safety
  -- $safeIntro
  , sAssert, isSafe, SExecutable(..)
  -- ** Satisfying a sequence of boolean conditions
  , solve

  -- ** Quick-checking
  , sbvQuickCheck

  -- * Running a symbolic computation
  , runSMT, runSMTWith

  -- * Optimization
  -- $optiIntro
  , OptimizeStyle(..), Penalty(..), Objective(..), minimize, maximize, assertSoft
  , ExtCW(..), GeneralizedCW(..)

  -- * Model extraction
  -- $modelExtraction

  -- ** Inspecting proof results
  -- $resultTypes
  , ThmResult(..), SatResult(..), AllSatResult(..), SafeResult(..), OptimizeResult(..), SMTResult(..)

  -- * IEEE-floating point numbers
  , IEEEFloating(..), IEEEFloatConvertable(..), RoundingMode(..), SRoundingMode, nan, infinity, sNaN, sInfinity
  -- ** Rounding modes
  , sRoundNearestTiesToEven, sRoundNearestTiesToAway, sRoundTowardPositive, sRoundTowardNegative, sRoundTowardZero, sRNE, sRNA, sRTP, sRTN, sRTZ
  -- ** Bit-pattern conversions
  , sFloatAsSWord32, sWord32AsSFloat, sDoubleAsSWord64, sWord64AsSDouble, blastSFloat, blastSDouble

  -- ** Programmable model extraction
  -- $programmableExtraction
  , SatModel(..), Modelable(..), displayModels, extractModels
  , getModelDictionaries, getModelValues, getModelUninterpretedValues

  -- * SMT Interface: Configurations and solvers
  , SMTConfig(..), Timing(..), SMTLibVersion(..), Solver(..), SMTSolver(..)
  , boolector, cvc4, yices, z3, mathSAT, abc, defaultSolverConfig, defaultSMTCfg, sbvCheckSolverInstallation, sbvAvailableSolvers
  , setLogic, setOption, setInfo, setTimeOut

  -- * Symbolic computations
  , Symbolic, output, SymWord(..)

  -- * Module exports
  -- $moduleExportIntro

  , module Data.Bits
  , module Data.Word
  , module Data.Int
  , module Data.Ratio
  ) where

import Control.Monad (filterM)

import qualified Control.Exception as C

import Data.SBV.Core.AlgReals
import Data.SBV.Core.Data
import Data.SBV.Core.Model
import Data.SBV.Core.Floating
import Data.SBV.Core.Splittable

import Data.SBV.Provers.Prover

import Data.SBV.Utils.Boolean
import Data.SBV.Utils.TDiff   (Timing(..))

import Data.Bits
import Data.Int
import Data.Ratio
import Data.Word

import qualified Language.Haskell.TH as TH
import Data.Generics
import Data.SBV.Control.Utils(SMTValue)

-- | Form the symbolic conjunction of a given list of boolean conditions. Useful in expressing
-- problems with constraints, like the following:
--
-- @
--   do [x, y, z] <- sIntegers [\"x\", \"y\", \"z\"]
--      solve [x .> 5, y + z .< x]
-- @
solve :: [SBool] -> Symbolic SBool
solve = return . bAnd

-- | Check whether the given solver is installed and is ready to go. This call does a
-- simple call to the solver to ensure all is well.
sbvCheckSolverInstallation :: SMTConfig -> IO Bool
sbvCheckSolverInstallation cfg = check `C.catch` (\(_ :: C.SomeException) -> return False)
  where check = do ThmResult r <- proveWith cfg $ \x -> (x+x) .== ((x*2) :: SWord8)
                   case r of
                     Unsatisfiable{} -> return True
                     _               -> return False

-- | The default configs corresponding to supported SMT solvers
defaultSolverConfig :: Solver -> SMTConfig
defaultSolverConfig Z3        = z3
defaultSolverConfig Yices     = yices
defaultSolverConfig Boolector = boolector
defaultSolverConfig CVC4      = cvc4
defaultSolverConfig MathSAT   = mathSAT
defaultSolverConfig ABC       = abc

-- | Return the known available solver configs, installed on your machine.
sbvAvailableSolvers :: IO [SMTConfig]
sbvAvailableSolvers = filterM sbvCheckSolverInstallation (map defaultSolverConfig [minBound .. maxBound])

-- If we get a program producing nothing (i.e., Symbolic ()), pretend it simply returns True.
-- This is useful since min/max calls and constraints will provide the context
instance Provable Goal where
  forAll_    a = forAll_    ((a >> return true) :: Predicate)
  forAll ns  a = forAll ns  ((a >> return true) :: Predicate)
  forSome_   a = forSome_   ((a >> return true) :: Predicate)
  forSome ns a = forSome ns ((a >> return true) :: Predicate)

-- | Equality as a proof method. Allows for
-- very concise construction of equivalence proofs, which is very typical in
-- bit-precise proofs.
infix 4 ===
class Equality a where
  (===) :: a -> a -> IO ThmResult

instance {-# OVERLAPPABLE #-} (SymWord a, EqSymbolic z) => Equality (SBV a -> z) where
  k === l = prove $ \a -> k a .== l a

instance {-# OVERLAPPABLE #-} (SymWord a, SymWord b, EqSymbolic z) => Equality (SBV a -> SBV b -> z) where
  k === l = prove $ \a b -> k a b .== l a b

instance {-# OVERLAPPABLE #-} (SymWord a, SymWord b, EqSymbolic z) => Equality ((SBV a, SBV b) -> z) where
  k === l = prove $ \a b -> k (a, b) .== l (a, b)

instance {-# OVERLAPPABLE #-} (SymWord a, SymWord b, SymWord c, EqSymbolic z) => Equality (SBV a -> SBV b -> SBV c -> z) where
  k === l = prove $ \a b c -> k a b c .== l a b c

instance {-# OVERLAPPABLE #-} (SymWord a, SymWord b, SymWord c, EqSymbolic z) => Equality ((SBV a, SBV b, SBV c) -> z) where
  k === l = prove $ \a b c -> k (a, b, c) .== l (a, b, c)

instance {-# OVERLAPPABLE #-} (SymWord a, SymWord b, SymWord c, SymWord d, EqSymbolic z) => Equality (SBV a -> SBV b -> SBV c -> SBV d -> z) where
  k === l = prove $ \a b c d -> k a b c d .== l a b c d

instance {-# OVERLAPPABLE #-} (SymWord a, SymWord b, SymWord c, SymWord d, EqSymbolic z) => Equality ((SBV a, SBV b, SBV c, SBV d) -> z) where
  k === l = prove $ \a b c d -> k (a, b, c, d) .== l (a, b, c, d)

instance {-# OVERLAPPABLE #-} (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, EqSymbolic z) => Equality (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> z) where
  k === l = prove $ \a b c d e -> k a b c d e .== l a b c d e

instance {-# OVERLAPPABLE #-} (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, EqSymbolic z) => Equality ((SBV a, SBV b, SBV c, SBV d, SBV e) -> z) where
  k === l = prove $ \a b c d e -> k (a, b, c, d, e) .== l (a, b, c, d, e)

instance {-# OVERLAPPABLE #-} (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, EqSymbolic z) => Equality (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> SBV f -> z) where
  k === l = prove $ \a b c d e f -> k a b c d e f .== l a b c d e f

instance {-# OVERLAPPABLE #-}
 (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, EqSymbolic z) => Equality ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> z) where
  k === l = prove $ \a b c d e f -> k (a, b, c, d, e, f) .== l (a, b, c, d, e, f)

instance {-# OVERLAPPABLE #-}
 (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, SymWord g, EqSymbolic z) => Equality (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> SBV f -> SBV g -> z) where
  k === l = prove $ \a b c d e f g -> k a b c d e f g .== l a b c d e f g

instance {-# OVERLAPPABLE #-} (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, SymWord g, EqSymbolic z) => Equality ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> z) where
  k === l = prove $ \a b c d e f g -> k (a, b, c, d, e, f, g) .== l (a, b, c, d, e, f, g)

-- | Make an enumeration a symbolic type.
mkSymbolicEnumeration :: TH.Name -> TH.Q [TH.Dec]
mkSymbolicEnumeration typeName = do
    let typeCon = TH.conT typeName
    [d| deriving instance Eq       $(typeCon)
        deriving instance Show     $(typeCon)
        deriving instance Ord      $(typeCon)
        deriving instance Read     $(typeCon)
        deriving instance Data     $(typeCon)
        deriving instance SymWord  $(typeCon)
        deriving instance HasKind  $(typeCon)
        deriving instance SMTValue $(typeCon)
        deriving instance SatModel $(typeCon)
      |]

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

= Incremental mode: Queries

SBV provides a wide variety of ways to utilize SMT-solvers, without requiring the user to
deal with the solvers themselves. While this mode is convenient, advanced users might need
access to the underlying solver, using the SMTLib language. For such use cases, SBV allows
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
On a multi-core machine, it might be desirable to try a given property using multiple SMT solvers,
using parallel threads. Even with machines with single-cores, threading can be helpful if you
want to try out multiple-solvers but do not know which one would work the best
for the problem at hand ahead of time.

The functions in this section allow proving/satisfiability-checking with multiple
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

Note that the function 'sbvAvailableSolvers' will return all the installed solvers, which can be
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
  s0 = 30 :: Int8
  s1 = 32 :: Int8]

What happens if we make sure to arrange for this invariant? Consider this version:

>>> let safeSub x y = ite (x .>= y) (sub x y) 0

Clearly, 'safeSub' must be safe. And indeed, SBV can prove that:

>>> safe (safeSub :: SInt8 -> SInt8 -> SInt8)
[sub: x >= y must hold!: No violations detected]

Note how we used 'sub' and 'safeSub' polymorphically. We only need to monomorphise our types when a proof
attempt is done, as we did in the 'safe' calls.

If required, the user can pass a 'CallStack' through the first argument to 'sAssert', which will be used
by SBV to print a diagnostic info to pinpoint the failure.

Also see "Data.SBV.Examples.Misc.NoDiv0" for the classic div-by-zero example.
-}


{- $optiIntro
  SBV can optimize metric functions, i.e., those that generate both bounded 'SIntN', 'SWordN', and unbounded 'SInteger'
  types, along with those produce 'SReal's. That is, it can find models satisfying all the constraints while minimizing
  or maximizing user given metrics. Currently, optimization requires the use of the z3 SMT solver as the backend,
  and a good review of these features is given
  in this paper: <http://www.easychair.org/publications/download/Z_-_Maximal_Satisfaction_with_Z3>.

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

== Multiple optimization goals

  Multiple goals can be specified, using the same syntax. In this case, the user gets to pick what style of
  optimization to perform, by passing the relevant 'OptimizeStyle' as the first argument to 'optimize'.

    * ['Lexicographic']. The solver will optimize the goals in the given order, optimizing
      the latter ones under the model that optimizes the previous ones.

    * ['Independent']. The solver will optimize the goals independently of each other. In this case the user will
      be presented a model for each goal given.

    * ['Pareto']. Finally, the user can query for pareto-fronts. A pareto front is an model such that no goal can be made
      "better" without making some other goal "worse."

      The optional number argument to 'Pareto' specifies the maximum number of pareto-fronts the user is asking
      to get. If 'Nothing', SBV will query for all pareto-fronts. Note that pareto-fronts can be infinite
      in number, so if 'Nothing' is used, there is a potential for infinitely waiting for the SBV-solver interaction
      to finish. (If you suspect this might be the case, run in 'verbose' mode to see the interaction and
      put a limiting factor appropriately.)

== Soft Assertions

  Related to optimization, SBV implements soft-asserts via 'assertSoft' calls. A soft assertion
  is a hint to the SMT solver that we would like a particular condition to hold if **possible*.
  That is, if there is a solution satisfying it, then we would like it to hold, but it can be violated
  if there is no way to satisfy it. Each soft-assertion can be associated with a numeric penalty for
  not satisfying it, hence turning it into an optimization problem.

  Note that 'assertSoft' works well with optimization goals ('minimize'/'maximize' etc.),
  and are most useful when we are optimizing a metric and thus some of the constraints
  can be relaxed with a penalty to obtain a good solution. Again
  see <http://www.easychair.org/publications/download/Z_-_Maximal_Satisfaction_with_Z3>
  for a good overview of the features in Z3 that SBV is providing the bridge for.

  A soft assertion can be specified in one of the following three main ways:

       @
         'assertSoft' "bounded_x" (x .< 5) 'DefaultPenalty'
         'assertSoft' "bounded_x" (x .< 5) ('Penalty' 2.3 Nothing)
         'assertSoft' "bounded_x" (x .< 5) ('Penalty' 4.7 (Just "group-1")) @

  In the first form, we are saying that the constraint @x .< 5@ must be satisfied, if possible,
  but if this constraint can not be satisfied to find a model, it can be violated with the default penalty of 1.

  In the second case, we are associating a penalty value of @2.3@.

  Finally in the third case, we are also associating this constraint with a group. The group
  name is only needed if we have classes of soft-constraints that should be considered together.

== Optimization examples

  The following examples illustrate the use of basic optimization routines:

     * "Data.SBV.Examples.Optimization.LinearOpt": Simple linear-optimization example.
     * "Data.SBV.Examples.Optimization.Production": Scheduling machines in a shop
     * "Data.SBV.Examples.Optimization.VM": Scheduling virtual-machines in a data-center
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
for 'free' (specialized at the given type), but they might be easier to use.
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

   * Extraction and concatenation: 'split', '#', and 'extend' (see the 'Splittable' class)

Usual arithmetic ('+', '-', '*', 'sQuotRem', 'sQuot', 'sRem', 'sDivMod', 'sDiv', 'sMod') and logical operations ('.<', '.<=', '.>', '.>=', '.==', './=') operations are
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

{- $constrainIntro
A constraint is a means for restricting the input domain of a formula. Here's a simple
example:

@
   do x <- 'exists' \"x\"
      y <- 'exists' \"y\"
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

  * In a 'quickCheck' call: The constraint acts as a filter for 'quickCheck';
    if the constraint does not hold, then the input value is considered to be irrelevant
    and is skipped. Note that this is similar to 'prove', but is stronger: We do not
    accept a test case to be valid just because the constraints fail on them, although
    semantically the implication does hold. We simply skip that test case as a /bad/
    test vector.

  * In a 'genTest' call: Similar to 'quickCheck' and 'prove': If a constraint
    does not hold, the input value is ignored and is not included in the test
    set.

A good use case (in fact the motivating use case) for 'constrain' is attaching a
constraint to a 'forall' or 'exists' variable at the time of its creation.
Also, the conjunctive semantics for 'sat' and the implicative
semantics for 'prove' simplify programming by choosing the correct interpretation
automatically. However, one should be aware of the semantic difference. For instance, in
the presence of constraints, formulas that are /provable/ are not necessarily
/satisfiable/. To wit, consider:

 @
    do x <- 'exists' \"x\"
       'constrain' $ x .< x
       return $ x .< (x :: 'SWord8')
 @

This predicate is unsatisfiable since no element of 'SWord8' is less than itself. But
it's (vacuously) true, since it excludes the entire domain of values, thus making the proof
trivial. Hence, this predicate is provable, but is not satisfiable. To make sure the given
constraints are not vacuous, the functions 'isVacuous' (and 'isVacuousWith') can be used.

Also note that this semantics imply that test case generation ('genTest') and quick-check
can take arbitrarily long in the presence of constraints, if the random input values generated
rarely satisfy the constraints. (As an extreme case, consider @'constrain' 'false'@.)

=== Named constraints and unsat cores

Constraints can be given names:

  @ 'namedConstraint' "a is at least 5" $ a .>= 5@

Such constraints are useful when used in conjunction with 'getUnsatCore' function
where the backend solver can be queried to obtain an unsat core in case the constraints are unsatisfiable.
This feature is enabled by the following tactic:

   @ tactic $ SetOptions [ProduceUnsatCores True] @

See "Data.SBV.Examples.Misc.UnsatCore" for an example use case.

=== Constraint vacuity

When adding constraints, one has to be careful about
making sure they are not inconsistent. The function 'isVacuous' can be use for this purpose.
Here is an example. Consider the following predicate:

    >>> let pred = do { x <- free "x"; constrain $ x .< x; return $ x .>= (5 :: SWord8) }

This predicate asserts that all 8-bit values are larger than 5, subject to the constraint that the
values considered satisfy @x .< x@, i.e., they are less than themselves. Since there are no values that
satisfy this constraint, the proof will pass vacuously:

    >>> prove pred
    Q.E.D.

We can use 'isVacuous' to make sure to see that the pass was vacuous:

    >>> isVacuous pred
    True

While the above example is trivial, things can get complicated if there are multiple constraints with
non-straightforward relations; so if constraints are used one should make sure to check the predicate
is not vacuously true. Here's an example that is not vacuous:

     >>> let pred' = do { x <- free "x"; constrain $ x .> 6; return $ x .>= (5 :: SWord8) }

This time the proof passes as expected:

     >>> prove pred'
     Q.E.D.

And the proof is not vacuous:

     >>> isVacuous pred'
     False

=== Checking for vacuity

As we discussed SBV does not check that a given constraints is not vacuous. That is, that it can never be satisfied. This is usually
the right behavior, since checking vacuity can be costly. The functions 'isVacuous' and 'isVacuousWith' should be used
to explicitly check for constraint vacuity if desired. Alternatively, the tactic:

  @ 'tactic' $  'CheckConstrVacuity' True @

can be given which will force SBV to run an explicit check that constraints are not vacuous. (And complain if they are!)
Note that this adds an extra call to the solver for each constraint, and thus can be rather costly.
-}

{- $uninterpreted
Users can introduce new uninterpreted sorts simply by defining a data-type in Haskell and registering it as such. The
following example demonstrates:

  @
     data B = B () deriving (Eq, Ord, Show, Read, Data, SymWord, HasKind, SatModel)
  @

(Note that you'll also need to use the language pragmas @DeriveDataTypeable@, @DeriveAnyClass@, and import @Data.Generics@ for the above to work.) 

This is all it takes to introduce 'B' as an uninterpreted sort in SBV, which makes the type @SBV B@ automagically become available as the type
of symbolic values that ranges over 'B' values. Note that the @()@ argument is important to distinguish it from enumerations, which will be
translated to proper SMT data-types.


Uninterpreted functions over both uninterpreted and regular sorts can be declared using the facilities introduced by
the 'Uninterpreted' class.
-}

{- $enumerations
If the uninterpreted sort definition takes the form of an enumeration (i.e., a simple data type with all nullary constructors), then SBV will actually
translate that as just such a data-type to SMT-Lib, and will use the constructors as the inhabitants of the said sort. A simple example is:

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

Now, the user can define

@
    type SX = SBV X
@

and treat @SX@ as a regular symbolic type ranging over the values @A@, @B@, and @C@. Such values can be compared for equality, and with the usual
other comparison operators, such as @.==@, @./=@, @.>@, @.>=@, @<@, and @<=@.

Note that in this latter case the type is no longer uninterpreted, but is properly represented as a simple enumeration of the said elements. A simple
query would look like:

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

Note that the result is properly typed as @X@ elements; these are not mere strings. So, in a 'getModelAssignment' scenario, the user can recover actual
elements of the domain and program further with those values as usual.

See "Data.SBV.Examples.Misc.Enumerate" for an extended example on how to use symbolic enumerations.
-}

{- $noteOnNestedQuantifiers
=== A note on reasoning in the presence of quantifers

Note that SBV allows reasoning with quantifiers: Inputs can be existentially or universally quantified. Predicates can be built
with arbitrary nesting of such quantifiers as well. However, SBV always /assumes/ that the input is in
prenex-normal form: <https://en.wikipedia.org/wiki/Prenex_normal_form>. That is,
all the input declarations are treated as happening at the beginning of a predicate, followed by the actual formula. Unfortunately,
the way predicates are written can be misleading at times, since symbolic inputs can be created at arbitrary points; interleaving them
with other code. The rule is simple, however: All inputs are assumed at the top, in the order declared, regardless of their quantifiers.
SBV will apply skolemization to get rid of existentials before sending predicates to backend solvers. However, if you do want nested
quantification, you will manually have to first convert to prenex-normal form (which produces an equisatisfiable but not necessarily
equivalent formula), and code that explicitly in SBV. See <https://github.com/LeventErkok/sbv/issues/256> for a detailed discussion
of this issue.
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

and they both express that at most /two/ of @b0@, @b1@, @b2@, and @b3@ can be 'true'.
However, the equivalent forms give rise to long formulas and the cardinality constraint
can get lost in the translation. The idea here is that if you use these functions instead, SBV will
produce better translations to SMTLib for more efficient solving of cardinality constraints, assuming
the backend solver supports them. Currently, only Z3 supports pseudo-booleans directly. For all other solvers,
SBV will translate these to equivalent terms that do not require special functions.
-}

{-# ANN module ("HLint: ignore Use import/export shortcut" :: String) #-}
