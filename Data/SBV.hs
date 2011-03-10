---------------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- (The sbv library is hosted at <http://github.com/LeventErkok/sbv>.
-- Comments, bug reports, and patches are always welcome.)
--
-- SBV: Symbolic Bit Vectors in Haskell
--
-- Express properties about bit-precise Haskell programs and automatically prove
-- them using SMT solvers.
--
-- >>> prove $ \x -> x `shiftL` 2 .== 4 * (x :: SWord8)
-- Q.E.D.
--
-- >>> prove $ forAll ["x"] $ \x -> x `shiftL` 2 .== (x :: SWord8)
-- Falsifiable. Counter-example:
--   x = 128 :: SWord8
--
-- The function 'prove' has the following type:
--
-- @
--     'prove' :: 'Provable' a => a -> 'IO' 'ThmResult'
-- @
--
-- The class 'Provable' comes with instances for n-ary predicates, for arbitrary n.
-- The predicates are just regular Haskell functions over symbolic signed and unsigned
-- bit-vectors. Functions for checking satisfiability ('sat' and 'allSat') are also
-- provided.
--
-- In particular, the sbv library introduces the types:
--
--   * 'SBool': Symbolic Booleans (bits)
--
--   * 'SWord8', 'SWord16', 'SWord32', 'SWord64': Symbolic Words (unsigned)
--
--   * 'SInt8',  'SInt16',  'SInt32',  'SInt64': Symbolic Ints (signed)
--
--   * 'SArray', 'SFunArray': Flat arrays of symbolic values
--
--   * Symbolic polynomials over GF(2^n), and polynomial arithmetic
--
--   * Uninterpreted constants and functions over symbolic values, with user
--     defined SMT-Lib axioms
--
-- The user can construct ordinary Haskell programs using these types, which behave
-- very similar to their concrete counterparts. In particular these types belong to the
-- standard classes 'Num', 'Bits', custom versions of 'Eq' ('EqSymbolic') 
-- and 'Ord' ('OrdSymbolic'), along with several other custom classes for simplifying
-- bit-precise programming with symbolic values. The framework takes full advantage
-- of Haskell's type inference to avoid many common mistakes.
--
-- Furthermore, predicates (i.e., functions that return 'SBool') built out of
-- these types can also be:
--
--   * proven correct via an external SMT solver (the 'prove' function)
--
--   * checked for satisfiability (the 'sat' and 'allSat' functions)
--
--   * quick-checked
--
-- If a predicate is not valid, 'prove' will return a counterexample: An
-- assignment to inputs such that the predicate fails. The 'sat' function will
-- return a satisfying assignment, if there is one. The 'allSat' function returns
-- all satisfying assignments, lazily.
--
-- The sbv library uses third-party SMT solvers via the standard SMT-Lib interface:
-- <http://goedel.cs.uiowa.edu/smtlib/>.
--
-- While the library is designed to work with any SMT-Lib compliant SMT-solver,
-- solver specific support is required for parsing counter-example/model data since
-- there is currently no agreed upon format for getting models from arbitrary SMT
-- solvers. (The SMT-Lib2 initiative will potentially address this issue in the
-- future, at which point the sbv library can be generalized as well.) Currently, we
-- only support the Yices SMT solver from SRI as far as the counter-example
-- and model generation support is concerned: <http://yices.csl.sri.com/>.
-- However, other solvers can be hooked up with relative ease.
--
-- You /should/ download and install Yices on your machine, and make sure the
-- @yices@ executable is in your path before using the sbv library, as it is the
-- current default solver. Alternatively, you can specify the location of yices
-- executable in the environment variable @SBV_YICES@ and the options to yices
-- in @SBV_YICES_OPTIONS@. (The default for the latter is '\"-m -f\"'.)
---------------------------------------------------------------------------------

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
  -- *** Arrays of symbolic values
  , SymArray(..), SArray, SFunArray, mkSFunArray
  -- ** Operations on symbolic words
  -- *** Word level
  , bitValue, setBitTo, oneIf, lsb, msb
  -- *** List level
  , allEqual, allDifferent
  -- *** Blasting/Unblasting
  , blastBE, blastLE, FromBits(..)
  -- *** Splitting, joining, and extending
  , Splittable(..)
  -- ** Polynomial arithmetic
  , Polynomial(..)
  -- ** Conditionals: Mergeable values
  , Mergeable(..)
  -- ** Symbolic equality
  , EqSymbolic(..)
  -- ** Symbolic ordering
  , OrdSymbolic(..)
  -- ** Division
  , BVDivisible(..)
  -- ** The Boolean class
  , Boolean(..)
  -- *** Generalizations of boolean operations
  , bAnd, bOr, bAny, bAll
  -- ** Pretty-printing and reading numbers in Hex & Binary
  , PrettyNum(..), readBin
  -- * Uninterpreted constants and functions
  , Uninterpreted(..)
  -- ** Accessing the handle
  , SBVUF, sbvUFName
  -- ** Adding axioms
  , addAxiom

  -- * Proving properties
  -- $proveIntro

  -- ** Predicates
  , Predicate, Provable(..), Equality(..)
  -- ** Proving properties
  , prove, proveWith, isTheorem, isTheoremWithin
  -- ** Checking satisfiability
  , sat, satWith, isSatisfiable, isSatisfiableWithin
  -- ** Finding all satisfying assignments
  , allSat, allSatWith, numberOfModels
  -- * Model extraction
  -- $modelExtraction

  -- ** Inspecting proof results
  -- $resultTypes
  , ThmResult(..), SatResult(..), AllSatResult(..), SMTResult(..)

  -- ** Programmable model extraction
  -- $programmableExtraction
  , SatModel(..), getModel, displayModels

  -- * SMT Interface: Configurations and solvers
  , SMTConfig(..), SMTSolver(..), defaultSMTCfg, verboseSMTCfg, timingSMTCfg, verboseTimingSMTCfg, timeout
  , yices

  -- * Symbolic computations
  , Symbolic, output, SymWord(..)

  -- * Getting SMT-Lib output (for offline analysis)
  , compileToSMTLib

  -- * Compiling symbolic programs to C
  , CgPgmBundle(..), compileToC, compileToC'

  -- * Module exports
  -- $moduleExportIntro

  , module Data.Bits
  , module Data.Word
  , module Data.Int
  ) where

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.Model
import Data.SBV.BitVectors.PrettyNum
import Data.SBV.BitVectors.Polynomial
import Data.SBV.BitVectors.Splittable
import Data.SBV.Compilers.C
import Data.SBV.Compilers.CodeGen
import Data.SBV.Provers.Prover
import Data.SBV.Utils.Boolean
import Data.Bits
import Data.Word
import Data.Int

-- Haddock section documentation
{- $progIntro
The SBV library is really two things:

  * A framework for writing bit-precise programs in Haskell

  * A framework for proving properties of such programs using SMT solvers

In this first section we will look at the constructs that will let us construct such
programs in Haskell. The goal is to have a "seamless" experience, i.e., program in
the usual Haskell style without distractions of symbolic coding. While Haskell helps
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
-}

{- $proveIntro
The SBV library provides a "push-button" verification system via automated SMT solving. The
design goal is to let SMT solvers be used without any knowledge of how SMT solvers work
or how different logics operate. The details are hidden behind the SBV framework, providing
Haskell programmers with a clean API that is unencumbered by the details of individual solvers.
To that end, we use the SMT-Lib standard (<http://goedel.cs.uiowa.edu/smtlib/>)
to communicate with arbitrary SMT solvers. Unfortunately,
the SMT-Lib version 1.X does not standardize how models are communicated back from solvers, so
there is some work in parsing individual SMT solver output. The 2.X version of the SMT-Lib
standard (not yet implemented by SMT solvers widely, unfortunately) will bring new standard features
for getting models; at which time the SBV framework can be modified into a truly plug-and-play
system where arbitrary SMT solvers can be used.
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
three modules to make any sensible use of the SBV functionality.
-}
