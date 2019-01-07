-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Client.BaseIO
-- Author    : Brian Schroeder, Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Monomorphized versions of functions for simplified client use via
-- @Data.SBV@, where we restrict the underlying monad to be IO.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts #-}

module Data.SBV.Client.BaseIO where

import Data.SBV.Core.Data      (HasKind, Kind, Outputtable, Penalty, SymArray,
                                SymVal, SBool, SBV, SChar, SDouble, SFloat,
                                SInt8, SInt16, SInt32, SInt64, SInteger, SList,
                                SReal, SString, SV, SWord8, SWord16, SWord32,
                                SWord64)
import Data.SBV.Core.Model     (Metric)
import Data.SBV.Core.Symbolic  (Objective, OptimizeStyle, Quantifier, Result,
                                Symbolic, SBVRunMode, SMTConfig, SVal)
import Data.SBV.Control.Types  (SMTOption)
import Data.SBV.Provers.Prover (Provable, SExecutable, ThmResult)
import Data.SBV.SMT.SMT        (AllSatResult, SafeResult, SatResult,
                                OptimizeResult)

import qualified Data.SBV.Core.Data      as Trans
import qualified Data.SBV.Core.Model     as Trans
import qualified Data.SBV.Core.Symbolic  as Trans
import qualified Data.SBV.Provers.Prover as Trans

-- Data.SBV.Provers.Prover:

-- | Turns a value into a universally quantified predicate, internally naming the inputs.
-- In this case the sbv library will use names of the form @s1, s2@, etc. to name these variables
-- Example:
--
-- >  forAll_ $ \(x::SWord8) y -> x `shiftL` 2 .== y
--
-- is a predicate with two arguments, captured using an ordinary Haskell function. Internally,
-- @x@ will be named @s0@ and @y@ will be named @s1@.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.forAll_'
forAll_ :: Provable a => a -> Symbolic SBool
forAll_ = Trans.forAll_

-- | Turns a value into a predicate, allowing users to provide names for the inputs.
-- If the user does not provide enough number of names for the variables, the remaining ones
-- will be internally generated. Note that the names are only used for printing models and has no
-- other significance; in particular, we do not check that they are unique. Example:
--
-- >  forAll ["x", "y"] $ \(x::SWord8) y -> x `shiftL` 2 .== y
--
-- This is the same as above, except the variables will be named @x@ and @y@ respectively,
-- simplifying the counter-examples when they are printed.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.forAll'
forAll :: Provable a => [String] -> a -> Symbolic SBool
forAll = Trans.forAll

-- | Turns a value into an existentially quantified predicate. (Indeed, 'exists' would have been
-- a better choice here for the name, but alas it's already taken.)
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.forSome_'
forSome_ :: Provable a => a -> Symbolic SBool
forSome_ = Trans.forSome_

-- | Version of 'forSome' that allows user defined names.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.forSome'
forSome :: Provable a => [String] -> a -> Symbolic SBool
forSome = Trans.forSome

-- | Prove a predicate, using the default solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.prove'
prove :: Provable a => a -> IO ThmResult
prove = Trans.prove

-- | Prove the predicate using the given SMT-solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.proveWith'
proveWith :: Provable a => SMTConfig -> a -> IO ThmResult
proveWith = Trans.proveWith

-- | Find a satisfying assignment for a predicate, using the default solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sat'
sat :: Provable a => a -> IO SatResult
sat = Trans.sat

-- | Find a satisfying assignment using the given SMT-solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.satWith'
satWith :: Provable a => SMTConfig -> a -> IO SatResult
satWith = Trans.satWith

-- | Find all satisfying assignments, using the default solver.
-- Equivalent to @'allSatWith' 'Data.SBV.defaultSMTCfg'@. See 'allSatWith' for details.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.allSat'
allSat :: Provable a => a -> IO AllSatResult
allSat = Trans.allSat

-- | Return all satisfying assignments for a predicate.
-- Note that this call will block until all satisfying assignments are found. If you have a problem
-- with infinitely many satisfying models (consider 'SInteger') or a very large number of them, you
-- might have to wait for a long time. To avoid such cases, use the 'Data.SBV.Core.Symbolic.allSatMaxModelCount'
-- parameter in the configuration.
--
-- NB. Uninterpreted constant/function values and counter-examples for array values are ignored for
-- the purposes of 'allSat'. That is, only the satisfying assignments modulo uninterpreted functions and
-- array inputs will be returned. This is due to the limitation of not having a robust means of getting a
-- function counter-example back from the SMT solver.
--  Find all satisfying assignments using the given SMT-solver
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.allSatWith'
allSatWith :: Provable a => SMTConfig -> a -> IO AllSatResult
allSatWith = Trans.allSatWith

-- | Optimize a given collection of `Objective`s.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.optimize'
optimize :: Provable a => OptimizeStyle -> a -> IO OptimizeResult
optimize = Trans.optimize

-- | Optimizes the objectives using the given SMT-solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.optimizeWith'
optimizeWith :: Provable a => SMTConfig -> OptimizeStyle -> a -> IO OptimizeResult
optimizeWith = Trans.optimizeWith

-- | Check if the constraints given are consistent, using the default solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.isVacuous'
isVacuous :: Provable a => a -> IO Bool
isVacuous = Trans.isVacuous

-- | Determine if the constraints are vacuous using the given SMT-solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.isVacuousWith'
isVacuousWith :: Provable a => SMTConfig -> a -> IO Bool
isVacuousWith = Trans.isVacuousWith

-- | Checks theoremhood using the default solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.isTheorem'
isTheorem :: Provable a => a -> IO Bool
isTheorem = Trans.isTheorem

-- | Check whether a given property is a theorem.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.isTheoremWith'
isTheoremWith :: Provable a => SMTConfig -> a -> IO Bool
isTheoremWith = Trans.isTheoremWith

-- | Checks satisfiability using the default solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.isSatisfiable'
isSatisfiable :: Provable a => a -> IO Bool
isSatisfiable = Trans.isSatisfiable

-- | Check whether a given property is satisfiable.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.isSatisfiableWith'
isSatisfiableWith :: Provable a => SMTConfig -> a -> IO Bool
isSatisfiableWith = Trans.isSatisfiableWith

-- | Run an arbitrary symbolic computation, equivalent to @'runSMTWith' 'Data.SBV.defaultSMTCfg'@
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.runSMT'
runSMT :: Symbolic a -> IO a
runSMT = Trans.runSMT

-- | Runs an arbitrary symbolic computation, exposed to the user in SAT mode
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.runSMTWith'
runSMTWith :: SMTConfig -> Symbolic a -> IO a
runSMTWith = Trans.runSMTWith

-- | NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sName_'
sName_ :: SExecutable IO a => a -> Symbolic ()
sName_ = Trans.sName_

-- | NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sName'
sName :: SExecutable IO a => [String] -> a -> Symbolic ()
sName = Trans.sName

-- | Check safety using the default solver.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.safe'
safe :: SExecutable IO a => a -> IO [SafeResult]
safe = Trans.safe

-- | Check if any of the 'Data.SBV.sAssert' calls can be violated.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.safeWith'
safeWith :: SExecutable IO a => SMTConfig -> a -> IO [SafeResult]
safeWith = Trans.safeWith

-- Data.SBV.Core.Data:

-- | Create a symbolic variable.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.mkSymSBV'
mkSymSBV :: Maybe Quantifier -> Kind -> Maybe String -> Symbolic (SBV a)
mkSymSBV = Trans.mkSymSBV

-- | Convert a symbolic value to an SV, inside the Symbolic monad
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sbvToSymSV'
sbvToSymSV :: SBV a -> Symbolic SV
sbvToSymSV = Trans.sbvToSymSV

-- | Mark an interim result as an output. Useful when constructing Symbolic programs
-- that return multiple values, or when the result is programmatically computed.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.output'
output :: Outputtable a => a -> Symbolic a
output = Trans.output

-- | Create a user named input (universal)
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.forall'
forall :: SymVal a => String -> Symbolic (SBV a)
forall = Trans.forall

-- | Create an automatically named input
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.forall_'
forall_ :: SymVal a => Symbolic (SBV a)
forall_ = Trans.forall_

-- | Get a bunch of new words
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.mkForallVars'
mkForallVars :: SymVal a => Int -> Symbolic [SBV a]
mkForallVars = Trans.mkForallVars

-- | Create an existential variable
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.exists'
exists :: SymVal a => String -> Symbolic (SBV a)
exists = Trans.exists

-- | Create an automatically named existential variable
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.exists_'
exists_ :: SymVal a => Symbolic (SBV a)
exists_ = Trans.exists_

-- | Create a bunch of existentials
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.mkExistVars'
mkExistVars :: SymVal a => Int -> Symbolic [SBV a]
mkExistVars = Trans.mkExistVars

-- | Create a free variable, universal in a proof, existential in sat
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.free'
free :: SymVal a => String -> Symbolic (SBV a)
free = Trans.free

-- | Create an unnamed free variable, universal in proof, existential in sat
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.free_'
free_ :: SymVal a => Symbolic (SBV a)
free_ = Trans.free_

-- | Create a bunch of free vars
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.mkFreeVars'
mkFreeVars :: SymVal a => Int -> Symbolic [SBV a]
mkFreeVars = Trans.mkFreeVars

-- | Similar to free; Just a more convenient name
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.symbolic'
symbolic :: SymVal a => String -> Symbolic (SBV a)
symbolic = Trans.symbolic

-- | Similar to mkFreeVars; but automatically gives names based on the strings
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.symbolics'
symbolics :: SymVal a => [String] -> Symbolic [SBV a]
symbolics = Trans.symbolics

-- | One stop allocator
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.mkSymVal'
mkSymVal :: SymVal a => Maybe Quantifier -> Maybe String -> Symbolic (SBV a)
mkSymVal = Trans.mkSymVal

-- | Create a new anonymous array, possibly with a default initial value.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.newArray_'
newArray_ :: (SymArray array, HasKind a, HasKind b) => Maybe (SBV b) -> Symbolic (array a b)
newArray_ = Trans.newArray_

-- | Create a named new array, possibly with a default initial value.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.newArray'
newArray :: (SymArray array, HasKind a, HasKind b) => String -> Maybe (SBV b) -> Symbolic (array a b)
newArray = Trans.newArray

-- Data.SBV.Core.Model:

-- | Generically make a symbolic var
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.genMkSymVar'
genMkSymVar :: Kind -> Maybe Quantifier -> Maybe String -> Symbolic (SBV a)
genMkSymVar = Trans.genMkSymVar

-- | Declare an 'SBool'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sBool'
sBool :: String -> Symbolic SBool
sBool = Trans.sBool

-- | Declare a list of 'SBool's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sBools'
sBools :: [String] -> Symbolic [SBool]
sBools = Trans.sBools

-- | Declare an 'SWord8'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWord8'
sWord8 :: String -> Symbolic SWord8
sWord8 = Trans.sWord8

-- | Declare a list of 'SWord8's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWord8s'
sWord8s :: [String] -> Symbolic [SWord8]
sWord8s = Trans.sWord8s

-- | Declare an 'SWord16'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWord16'
sWord16 :: String -> Symbolic SWord16
sWord16 = Trans.sWord16

-- | Declare a list of 'SWord16's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWord16s'
sWord16s :: [String] -> Symbolic [SWord16]
sWord16s = Trans.sWord16s

-- | Declare an 'SWord32'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWord32'
sWord32 :: String -> Symbolic SWord32
sWord32 = Trans.sWord32

-- | Declare a list of 'SWord32's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWord32s'
sWord32s :: [String] -> Symbolic [SWord32]
sWord32s = Trans.sWord32s

-- | Declare an 'SWord64'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWord64'
sWord64 :: String -> Symbolic SWord64
sWord64 = Trans.sWord64

-- | Declare a list of 'SWord64's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWord64s'
sWord64s :: [String] -> Symbolic [SWord64]
sWord64s = Trans.sWord64s

-- | Declare an 'SInt8'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInt8'
sInt8 :: String -> Symbolic SInt8
sInt8 = Trans.sInt8

-- | Declare a list of 'SInt8's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInt8s'
sInt8s :: [String] -> Symbolic [SInt8]
sInt8s = Trans.sInt8s

-- | Declare an 'SInt16'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInt16'
sInt16 :: String -> Symbolic SInt16
sInt16 = Trans.sInt16

-- | Declare a list of 'SInt16's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInt16s'
sInt16s :: [String] -> Symbolic [SInt16]
sInt16s = Trans.sInt16s

-- | Declare an 'SInt32'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInt32'
sInt32 :: String -> Symbolic SInt32
sInt32 = Trans.sInt32

-- | Declare a list of 'SInt32's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInt32s'
sInt32s :: [String] -> Symbolic [SInt32]
sInt32s = Trans.sInt32s

-- | Declare an 'SInt64'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInt64'
sInt64 :: String -> Symbolic SInt64
sInt64 = Trans.sInt64

-- | Declare a list of 'SInt64's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInt64s'
sInt64s :: [String] -> Symbolic [SInt64]
sInt64s = Trans.sInt64s

-- | Declare an 'SInteger'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sInteger'
sInteger :: String -> Symbolic SInteger
sInteger = Trans.sInteger

-- | Declare a list of 'SInteger's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sIntegers'
sIntegers :: [String] -> Symbolic [SInteger]
sIntegers = Trans.sIntegers

-- | Declare an 'SReal'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sReal'
sReal :: String -> Symbolic SReal
sReal = Trans.sReal

-- | Declare a list of 'SReal's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sReals'
sReals :: [String] -> Symbolic [SReal]
sReals = Trans.sReals

-- | Declare an 'SFloat'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sFloat'
sFloat :: String -> Symbolic SFloat
sFloat = Trans.sFloat

-- | Declare a list of 'SFloat's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sFloats'
sFloats :: [String] -> Symbolic [SFloat]
sFloats = Trans.sFloats

-- | Declare an 'SDouble'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sDouble'
sDouble :: String -> Symbolic SDouble
sDouble = Trans.sDouble

-- | Declare a list of 'SDouble's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sDoubles'
sDoubles :: [String] -> Symbolic [SDouble]
sDoubles = Trans.sDoubles

-- | Declare an 'SChar'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sChar'
sChar :: String -> Symbolic SChar
sChar = Trans.sChar

-- | Declare an 'SString'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sString'
sString :: String -> Symbolic SString
sString = Trans.sString

-- | Declare a list of 'SChar's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sChars'
sChars :: [String] -> Symbolic [SChar]
sChars = Trans.sChars

-- | Declare a list of 'SString's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sStrings'
sStrings :: [String] -> Symbolic [SString]
sStrings = Trans.sStrings

-- | Declare an 'SList'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sList'
sList :: SymVal a => String -> Symbolic (SList a)
sList = Trans.sList

-- | Declare a list of 'SList's
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sLists'
sLists :: SymVal a => [String] -> Symbolic [SList a]
sLists = Trans.sLists

-- | Declare a tuple.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sTuple'
sTuple :: SymVal tup => String -> Symbolic (SBV tup)
sTuple = Trans.sTuple

-- | Declare a list of tuples.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sTuples'
sTuples :: SymVal tup => [String] -> Symbolic [SBV tup]
sTuples = Trans.sTuples

-- | Form the symbolic conjunction of a given list of boolean conditions. Useful in expressing
-- problems with constraints, like the following:
--
-- @
--   sat $ do [x, y, z] <- sIntegers [\"x\", \"y\", \"z\"]
--            solve [x .> 5, y + z .< x]
-- @
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.solve'
solve :: [SBool] -> Symbolic SBool
solve = Trans.solve

-- | Introduce a soft assertion, with an optional penalty
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.assertWithPenalty'
assertWithPenalty :: String -> SBool -> Penalty -> Symbolic ()
assertWithPenalty = Trans.assertWithPenalty

-- | Minimize a named metric
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.minimize'
minimize :: Metric a => String -> a -> Symbolic ()
minimize = Trans.minimize

-- | Maximize a named metric
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.maximize'
maximize :: Metric a => String -> a -> Symbolic ()
maximize = Trans.maximize

-- Data.SBV.Core.Symbolic:

-- | Convert a symbolic value to an SV, inside the Symbolic monad
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.svToSymSV'
svToSymSV :: SVal -> Symbolic SV
svToSymSV = Trans.svToSymSV

-- | Create an N-bit symbolic unsigned named variable
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWordN'
sWordN :: Int -> String -> Symbolic SVal
sWordN = Trans.sWordN

-- | Create an N-bit symbolic unsigned unnamed variable
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sWordN_'
sWordN_ :: Int -> Symbolic SVal
sWordN_ = Trans.sWordN_

-- | Create an N-bit symbolic signed named variable
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sIntN'
sIntN :: Int -> String -> Symbolic SVal
sIntN = Trans.sIntN

-- | Create an N-bit symbolic signed unnamed variable
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.sIntN_'
sIntN_ :: Int -> Symbolic SVal
sIntN_ = Trans.sIntN_

-- | Add a user specified axiom to the generated SMT-Lib file. The first argument is a mere
-- string, use for commenting purposes. The second argument is intended to hold the multiple-lines
-- of the axiom text as expressed in SMT-Lib notation. Note that we perform no checks on the axiom
-- itself, to see whether it's actually well-formed or is sensical by any means.
-- A separate formalization of SMT-Lib would be very useful here.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.addAxiom'
addAxiom :: String -> [String] -> Symbolic ()
addAxiom = Trans.addAxiom

-- | Run a symbolic computation, and return a extra value paired up with the 'Result'
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.runSymbolic'
runSymbolic :: SBVRunMode -> Symbolic a -> IO (a, Result)
runSymbolic = Trans.runSymbolic

-- | Add a new option
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.addNewSMTOption'
addNewSMTOption :: SMTOption -> Symbolic ()
addNewSMTOption = Trans.addNewSMTOption

-- | Handling constraints
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.imposeConstraint'
imposeConstraint :: Bool -> [(String, String)] -> SVal -> Symbolic ()
imposeConstraint = Trans.imposeConstraint

-- | Add an optimization goal
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.addSValOptGoal'
addSValOptGoal :: Objective SVal -> Symbolic ()
addSValOptGoal = Trans.addSValOptGoal

-- | Mark an interim result as an output. Useful when constructing Symbolic programs
-- that return multiple values, or when the result is programmatically computed.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.outputSVal'
outputSVal :: SVal -> Symbolic ()
outputSVal = Trans.outputSVal
