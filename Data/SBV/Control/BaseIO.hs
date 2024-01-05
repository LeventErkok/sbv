-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Control.BaseIO
-- Copyright : (c) Brian Schroeder
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Monomorphized versions of functions for simplified client use via
-- @Data.SBV.Control@, where we restrict the underlying monad to be IO.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Control.BaseIO where

import Data.SBV.Control.Query (Assignment)
import Data.SBV.Control.Types (CheckSatResult, SMTInfoFlag, SMTInfoResponse, SMTOption, SMTReasonUnknown)
import Data.SBV.Core.Concrete (CV)
import Data.SBV.Core.Data     (HasKind, Symbolic, SymArray, SymVal, SBool, SBV, SBVType, Lambda(..))
import Data.SBV.Core.Symbolic (Query, QueryContext, QueryState, State, SMTModel, SMTResult, SV, Name, SymbolicT)

import qualified Data.SBV.Control.Query as Trans
import qualified Data.SBV.Control.Utils as Trans

import Data.SBV.Utils.SExpr (SExpr)

-- Data.SBV.Control.Query

-- | Ask solver for info.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.getInfo'
getInfo :: SMTInfoFlag -> Query SMTInfoResponse
getInfo = Trans.getInfo

-- | Retrieve the value of an 'SMTOption.' The curious function argument is on purpose here,
-- simply pass the constructor name. Example: the call @'getOption' 'Data.SBV.Control.ProduceUnsatCores'@ will return
-- either @Nothing@ or @Just (ProduceUnsatCores True)@ or @Just (ProduceUnsatCores False)@.
--
-- Result will be 'Nothing' if the solver does not support this option.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.getOption'
getOption :: (a -> SMTOption) -> Query (Maybe SMTOption)
getOption = Trans.getOption

-- | Get the reason unknown. Only internally used.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.getUnknownReason'
getUnknownReason :: Query SMTReasonUnknown
getUnknownReason = Trans.getUnknownReason

-- | Get the observables recorded during a query run.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.getObservables'
getObservables :: Query [(Name, CV)]
getObservables = Trans.getObservables

-- | Get the uninterpreted constants/functions recorded during a run.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.getUIs'
getUIs :: Query [(String, (Bool, Maybe [String], SBVType))]
getUIs = Trans.getUIs

-- | Issue check-sat and get an SMT Result out.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.getSMTResult'
getSMTResult :: Query SMTResult
getSMTResult = Trans.getSMTResult

-- | Issue check-sat and get results of a lexicographic optimization.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.getLexicographicOptResults'
getLexicographicOptResults :: Query SMTResult
getLexicographicOptResults = Trans.getLexicographicOptResults

-- | Issue check-sat and get results of an independent (boxed) optimization.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.getIndependentOptResults'
getIndependentOptResults :: [String] -> Query [(String, SMTResult)]
getIndependentOptResults = Trans.getIndependentOptResults

-- | Construct a pareto-front optimization result
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.getParetoOptResults'
getParetoOptResults :: Maybe Int -> Query (Bool, [SMTResult])
getParetoOptResults = Trans.getParetoOptResults

-- | Collect model values. It is implicitly assumed that we are in a check-sat
-- context. See 'getSMTResult' for a variant that issues a check-sat first and
-- returns an 'SMTResult'.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.getModel'
getModel :: Query SMTModel
getModel = Trans.getModel

-- | Check for satisfiability, under the given conditions. Similar to 'Data.SBV.Control.checkSat' except it allows making
-- further assumptions as captured by the first argument of booleans. (Also see 'checkSatAssumingWithUnsatisfiableSet'
-- for a variant that returns the subset of the given assumptions that led to the 'Data.SBV.Control.Unsat' conclusion.)
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.checkSatAssuming'
checkSatAssuming :: [SBool] -> Query CheckSatResult
checkSatAssuming = Trans.checkSatAssuming

-- | Check for satisfiability, under the given conditions. Returns the unsatisfiable
-- set of assumptions. Similar to 'Data.SBV.Control.checkSat' except it allows making further assumptions
-- as captured by the first argument of booleans. If the result is 'Data.SBV.Control.Unsat', the user will
-- also receive a subset of the given assumptions that led to the 'Data.SBV.Control.Unsat' conclusion. Note
-- that while this set will be a subset of the inputs, it is not necessarily guaranteed to be minimal.
--
-- You must have arranged for the production of unsat assumptions
-- first via
--
-- @
--     'Data.SBV.setOption' $ 'Data.SBV.Control.ProduceUnsatAssumptions' 'True'
-- @
--
-- for this call to not error out!
--
-- Usage note: 'getUnsatCore' is usually easier to use than 'checkSatAssumingWithUnsatisfiableSet', as it
-- allows the use of named assertions, as obtained by 'Data.SBV.namedConstraint'. If 'getUnsatCore'
-- fills your needs, you should definitely prefer it over 'checkSatAssumingWithUnsatisfiableSet'.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.checkSatAssumingWithUnsatisfiableSet'
checkSatAssumingWithUnsatisfiableSet :: [SBool] -> Query (CheckSatResult, Maybe [SBool])
checkSatAssumingWithUnsatisfiableSet = Trans.checkSatAssumingWithUnsatisfiableSet

-- | The current assertion stack depth, i.e., #push - #pops after start. Always non-negative.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.getAssertionStackDepth'
getAssertionStackDepth :: Query Int
getAssertionStackDepth = Trans.getAssertionStackDepth

-- | Run the query in a new assertion stack. That is, we push the context, run the query
-- commands, and pop it back.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.inNewAssertionStack'
inNewAssertionStack :: Query a -> Query a
inNewAssertionStack = Trans.inNewAssertionStack

-- | Push the context, entering a new one. Pushes multiple levels if /n/ > 1.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.push'
push :: Int -> Query ()
push = Trans.push

-- | Pop the context, exiting a new one. Pops multiple levels if /n/ > 1. It's an error to pop levels that don't exist.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.pop'
pop :: Int -> Query ()
pop = Trans.pop

-- | Search for a result via a sequence of case-splits, guided by the user. If one of
-- the conditions lead to a satisfiable result, returns @Just@ that result. If none of them
-- do, returns @Nothing@. Note that we automatically generate a coverage case and search
-- for it automatically as well. In that latter case, the string returned will be "Coverage".
-- The first argument controls printing progress messages  See "Documentation.SBV.Examples.Queries.CaseSplit"
-- for an example use case.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.caseSplit'
caseSplit :: Bool -> [(String, SBool)] -> Query (Maybe (String, SMTResult))
caseSplit = Trans.caseSplit

-- | Reset the solver, by forgetting all the assertions. However, bindings are kept as is,
-- as opposed to a full reset of the solver. Use this variant to clean-up the solver
-- state while leaving the bindings intact. Pops all assertion levels. Declarations and
-- definitions resulting from the 'Data.SBV.setLogic' command are unaffected. Note that SBV
-- implicitly uses global-declarations, so bindings will remain intact.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.resetAssertions'
resetAssertions :: Query ()
resetAssertions = Trans.resetAssertions

-- | Echo a string. Note that the echoing is done by the solver, not by SBV.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.echo'
echo :: String -> Query ()
echo = Trans.echo

-- | Exit the solver. This action will cause the solver to terminate. Needless to say,
-- trying to communicate with the solver after issuing "exit" will simply fail.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.exit'
exit :: Query ()
exit = Trans.exit

-- | Retrieve the unsat-core. Note you must have arranged for
-- unsat cores to be produced first via
--
-- @
--     'Data.SBV.setOption' $ 'Data.SBV.Control.ProduceUnsatCores' 'True'
-- @
--
-- for this call to not error out!
--
-- NB. There is no notion of a minimal unsat-core, in case unsatisfiability can be derived
-- in multiple ways. Furthermore, Z3 does not guarantee that the generated unsat
-- core does not have any redundant assertions either, as doing so can incur a performance penalty.
-- (There might be assertions in the set that is not needed.) To ensure all the assertions
-- in the core are relevant, use:
--
-- @
--     'Data.SBV.setOption' $ 'Data.SBV.Control.OptionKeyword' ":smt.core.minimize" ["true"]
-- @
--
-- Note that this only works with Z3.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.getUnsatCore'
getUnsatCore :: Query [String]
getUnsatCore = Trans.getUnsatCore

-- | Retrieve the proof. Note you must have arranged for
-- proofs to be produced first via
--
-- @
--     'Data.SBV.setOption' $ 'Data.SBV.Control.ProduceProofs' 'True'
-- @
--
-- for this call to not error out!
--
-- A proof is simply a 'String', as returned by the solver. In the future, SBV might
-- provide a better datatype, depending on the use cases. Please get in touch if you
-- use this function and can suggest a better API.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.getProof'
getProof :: Query String
getProof = Trans.getProof

-- | Interpolant extraction for MathSAT. Compare with 'getInterpolantZ3', which performs
-- similar function (but with a different use model) in Z3.
--
-- Retrieve an interpolant after an 'Data.SBV.Control.Unsat' result is obtained. Note you must have arranged for
-- interpolants to be produced first via
--
-- @
--     'Data.SBV.setOption' $ 'Data.SBV.Control.ProduceInterpolants' 'True'
-- @
--
-- for this call to not error out!
--
-- To get an interpolant for a pair of formulas @A@ and @B@, use a 'Data.SBV.constrainWithAttribute' call to attach
-- interplation groups to @A@ and @B@. Then call 'getInterpolantMathSAT' @[\"A\"]@, assuming those are the names
-- you gave to the formulas in the @A@ group.
--
-- An interpolant for @A@ and @B@ is a formula @I@ such that:
--
-- @
--        A .=> I
--    and B .=> sNot I
-- @
--
-- That is, it's evidence that @A@ and @B@ cannot be true together
-- since @A@ implies @I@ but @B@ implies @not I@; establishing that @A@ and @B@ cannot
-- be satisfied at the same time. Furthermore, @I@ will have only the symbols that are common
-- to @A@ and @B@.
--
-- NB. Interpolant extraction isn't standardized well in SMTLib. Currently both MathSAT and Z3
-- support them, but with slightly differing APIs. So, we support two APIs with slightly
-- differing types to accommodate both. See "Documentation.SBV.Examples.Queries.Interpolants" for example
-- usages in these solvers.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.getInterpolantMathSAT'
getInterpolantMathSAT :: [String] -> Query String
getInterpolantMathSAT = Trans.getInterpolantMathSAT

-- | Interpolant extraction for z3. Compare with 'getInterpolantMathSAT', which performs
-- similar function (but with a different use model) in MathSAT.
--
-- Unlike the MathSAT variant, you should simply call 'getInterpolantZ3' on symbolic booleans
-- to retrieve the interpolant. Do not call `checkSat` or create named constraints. This makes it
-- harder to identify formulas, but the current state of affairs in interpolant API requires this kludge.
--
-- An interpolant for @A@ and @B@ is a formula @I@ such that:
--
-- @
--        A ==> I
--    and B ==> not I
-- @
--
-- That is, it's evidence that @A@ and @B@ cannot be true together
-- since @A@ implies @I@ but @B@ implies @not I@; establishing that @A@ and @B@ cannot
-- be satisfied at the same time. Furthermore, @I@ will have only the symbols that are common
-- to @A@ and @B@.
--
-- In Z3, interpolants generalize to sequences: If you pass more than two formulas, then you will get
-- a sequence of interpolants. In general, for @N@ formulas that are not satisfiable together, you will be
-- returned @N-1@ interpolants. If formulas are @A1 .. An@, then interpolants will be @I1 .. I(N-1)@, such
-- that @A1 ==> I1@, @A2 /\\ I1 ==> I2@, @A3 /\\ I2 ==> I3@, ..., and finally @AN ===> not I(N-1)@.
--
-- Currently, SBV only returns simple and sequence interpolants, and does not support tree-interpolants.
-- If you need these, please get in touch. Furthermore, the result will be a list of mere strings representing the
-- interpolating formulas, as opposed to a more structured type. Please get in touch if you use this function and can
-- suggest a better API.
--
-- NB. Interpolant extraction isn't standardized well in SMTLib. Currently both MathSAT and Z3
-- support them, but with slightly differing APIs. So, we support two APIs with slightly
-- differing types to accommodate both. See "Documentation.SBV.Examples.Queries.Interpolants" for example
-- usages in these solvers.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.getInterpolantZ3'
getInterpolantZ3 :: [SBool] -> Query String
getInterpolantZ3 = Trans.getInterpolantZ3

-- | Get an abduct. The first argument is a conjecture. The return value will be an assertion
-- such that in addition with the existing assertions you have, will imply this conjecture.
-- The second argument is the grammar which guides the synthesis of this abduct, if given.
-- Note that SBV doesn't do any checking on the grammar. See the relevant documentation on CVC5
-- for details.
--
-- NB. Before you use this function, make sure to call
--
-- @
--      setOption $ ProduceAbducts True
-- @
--
-- to enable abduct generation.
getAbduct :: Maybe String -> String -> SBool -> Query String
getAbduct = Trans.getAbduct

-- | Get the next abduct. Only call this after the first call to 'getAbduct' goes through. You can call
-- it repeatedly to get a different abduct.
getAbductNext :: Query String
getAbductNext = Trans.getAbductNext

-- | Retrieve assertions. Note you must have arranged for
-- assertions to be available first via
--
-- @
--     'Data.SBV.setOption' $ 'Data.SBV.Control.ProduceAssertions' 'True'
-- @
--
-- for this call to not error out!
--
-- Note that the set of assertions returned is merely a list of strings, just like the
-- case for 'getProof'. In the future, SBV might provide a better datatype, depending
-- on the use cases. Please get in touch if you use this function and can suggest
-- a better API.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.getAssertions'
getAssertions :: Query [String]
getAssertions = Trans.getAssertions

-- | Retrieve the assignment. This is a lightweight version of 'getValue', where the
-- solver returns the truth value for all named subterms of type 'Bool'.
--
-- You must have first arranged for assignments to be produced via
--
-- @
--     'Data.SBV.setOption' $ 'Data.SBV.Control.ProduceAssignments' 'True'
-- @
--
-- for this call to not error out!
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.getAssignment'
getAssignment :: Query [(String, Bool)]
getAssignment = Trans.getAssignment

-- | Produce the query result from an assignment.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.mkSMTResult'
mkSMTResult :: [Assignment] -> Query SMTResult
mkSMTResult = Trans.mkSMTResult

-- Data.SBV.Control.Utils

-- | Perform an arbitrary IO action.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.io'
io :: IO a -> Query a
io = Trans.io

-- | Modify the query state
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.modifyQueryState'
modifyQueryState :: (QueryState -> QueryState) -> Query ()
modifyQueryState = Trans.modifyQueryState

-- | Execute in a new incremental context
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.inNewContext'
inNewContext :: (State -> IO a) -> Query a
inNewContext = Trans.inNewContext

-- | Similar to 'freshVar', except creates unnamed variable.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.freshVar_'
freshVar_ :: SymVal a => Query (SBV a)
freshVar_ = Trans.freshVar_

-- | Create a fresh variable in query mode. You should prefer
-- creating input variables using 'Data.SBV.sBool', 'Data.SBV.sInt32', etc., which act
-- as primary inputs to the model. Use 'freshVar' only in query mode for anonymous temporary variables.
-- Note that 'freshVar' should hardly be needed: Your input variables and symbolic expressions
-- should suffice for -- most major use cases.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.freshVar'
freshVar :: SymVal a => String -> Query (SBV a)
freshVar = Trans.freshVar

-- | Similar to 'freshArray', except creates unnamed array.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.freshArray_'
freshArray_ :: (SymArray array, HasKind a, HasKind b) => Maybe (SBV b) -> Query (array a b)
freshArray_ = Trans.freshArray_

-- | Create a fresh array in query mode. Again, you should prefer
-- creating arrays before the queries start using 'Data.SBV.newArray', but this
-- method can come in handy in occasional cases where you need a new array
-- after you start the query based interaction.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.freshArray'
freshArray :: (SymArray array, HasKind a, HasKind b) => String -> Maybe (SBV b) -> Query (array a b)
freshArray = Trans.freshArray

-- | Create a fresh lambda array
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.freshLambdaArray'
freshLambdaArray :: (HasKind a, HasKind b, Lambda (SymbolicT IO) (a -> b), SymArray array) => String -> (a -> b) -> Query (array a b)
freshLambdaArray = Trans.freshLambdaArray

-- | Create a fresh lambda array, unnamed
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.freshLambdaArray_'
freshLambdaArray_ :: (HasKind a, HasKind b, Lambda (SymbolicT IO) (a -> b), SymArray array) => (a -> b) -> Query (array a b)
freshLambdaArray_ = Trans.freshLambdaArray_

-- | If 'Data.SBV.verbose' is 'True', print the message, useful for debugging messages
-- in custom queries. Note that 'Data.SBV.redirectVerbose' will be respected: If a
-- file redirection is given, the output will go to the file.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.queryDebug'
queryDebug :: [String] -> Query ()
queryDebug = Trans.queryDebug

-- | Send a string to the solver, and return the response
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.ask'
ask :: String -> Query String
ask = Trans.ask

-- | Send a string to the solver. If the first argument is 'True', we will require
-- a "success" response as well. Otherwise, we'll fire and forget.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.send'
send :: Bool -> String -> Query ()
send = Trans.send

-- | Retrieve a responses from the solver until it produces a synchronization tag. We make the tag
-- unique by attaching a time stamp, so no need to worry about getting the wrong tag unless it happens
-- in the very same picosecond! We return multiple valid s-expressions till the solver responds with the tag.
-- Should only be used for internal tasks or when we want to synchronize communications, and not on a
-- regular basis! Use 'send'/'ask' for that purpose. This comes in handy, however, when solvers respond
-- multiple times as in optimization for instance, where we both get a check-sat answer and some objective values.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.retrieveResponse'
retrieveResponse :: String -> Maybe Int -> Query [String]
retrieveResponse = Trans.retrieveResponse

-- | Get the value of a term.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.getValue'
getValue :: SymVal a => SBV a -> Query a
getValue = Trans.getValue

-- | Get the value of an uninterpreted sort, as a String
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.getUninterpretedValue'
getUninterpretedValue :: HasKind a => SBV a -> Query String
getUninterpretedValue = Trans.getUninterpretedValue

-- | Get the value of an uninterpreted function, as a list of domain, value pairs.
-- The final value is the "else" clause, i.e., what the function maps values outside
-- of the domain of the first list. If the result is not a value-association, then we get a string
-- representation and the triple of whether it's curried, the argument list given by the user, and the s-expression as parsed
-- by SBV from the SMT solver.
getFunction :: (SymVal a, SymVal r, Trans.SMTFunction fun a r) => fun -> Query (Either (String, (Bool, Maybe [String], SExpr)) ([(a, r)], r))
getFunction = Trans.getFunction

-- | Get the value of a term. If the kind is Real and solver supports decimal approximations,
-- we will "squash" the representations.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.getValueCV'
getValueCV :: Maybe Int -> SV -> Query CV
getValueCV = Trans.getValueCV

-- | Get the value of an uninterpreted value
getUICVal :: Maybe Int -> (String, (Bool, Maybe [String], SBVType)) -> Query CV
getUICVal = Trans.getUICVal

-- | Get the value of an uninterpreted function as an association list
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.getUIFunCVAssoc'
getUIFunCVAssoc :: Maybe Int -> (String, (Bool, Maybe [String], SBVType)) -> Query (Either String ([([CV], CV)], CV))
getUIFunCVAssoc = Trans.getUIFunCVAssoc

-- | Check for satisfiability.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.checkSat'
checkSat :: Query CheckSatResult
checkSat = Trans.checkSat

-- | Ensure that the current context is satisfiable. If not, this function will throw an error.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.ensureSat'
ensureSat :: Query ()
ensureSat = Trans.ensureSat

-- | Check for satisfiability with a custom check-sat-using command.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.checkSatUsing'
checkSatUsing :: String -> Query CheckSatResult
checkSatUsing = Trans.checkSatUsing

-- | Retrieve the set of unsatisfiable assumptions, following a call to 'Data.SBV.Control.checkSatAssumingWithUnsatisfiableSet'. Note that
-- this function isn't exported to the user, but rather used internally. The user simple calls 'Data.SBV.Control.checkSatAssumingWithUnsatisfiableSet'.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.getUnsatAssumptions'
getUnsatAssumptions :: [String] -> [(String, a)] -> Query [a]
getUnsatAssumptions = Trans.getUnsatAssumptions

-- | Timeout a query action, typically a command call to the underlying SMT solver.
-- The duration is in microseconds (@1\/10^6@ seconds). If the duration
-- is negative, then no timeout is imposed. When specifying long timeouts, be careful not to exceed
-- @maxBound :: Int@. (On a 64 bit machine, this bound is practically infinite. But on a 32 bit
-- machine, it corresponds to about 36 minutes!)
--
-- Semantics: The call @timeout n q@ causes the timeout value to be applied to all interactive calls that take place
-- as we execute the query @q@. That is, each call that happens during the execution of @q@ gets a separate
-- time-out value, as opposed to one timeout value that limits the whole query. This is typically the intended behavior.
-- It is advisable to apply this combinator to calls that involve a single call to the solver for
-- finer control, as opposed to an entire set of interactions. However, different use cases might call for different scenarios.
--
-- If the solver responds within the time-out specified, then we continue as usual. However, if the backend solver times-out
-- using this mechanism, there is no telling what the state of the solver will be. Thus, we raise an error in this case.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.timeout'
timeout :: Int -> Query a -> Query a
timeout = Trans.timeout

-- | Bail out if we don't get what we expected
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.unexpected'
unexpected :: String -> String -> String -> Maybe [String] -> String -> Maybe [String] -> Query a
unexpected = Trans.unexpected

-- | Execute a query.
--
-- NB. For a version which generalizes over the underlying monad, see 'Data.SBV.Trans.Control.executeQuery'
executeQuery :: QueryContext -> Query a -> Symbolic a
executeQuery = Trans.executeQuery
