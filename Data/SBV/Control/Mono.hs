-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Control.Mono
-- Copyright   :  (c) Brian Schroeder, Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Monomorphized versions of functions for simplified client use via
-- @Data.SBV.Control@.
-----------------------------------------------------------------------------

module Data.SBV.Control.Mono where

import Data.SBV.Control.Query (Assignment)
import Data.SBV.Control.Types (CheckSatResult, SMTInfoFlag, SMTInfoResponse,
                               SMTOption, SMTReasonUnknown)
import Data.SBV.Control.Utils (SMTValue)
import Data.SBV.Core.Concrete (CW)
import Data.SBV.Core.Data     (HasKind, Symbolic, SymArray, SymWord, SBool,
                               SBV)
import Data.SBV.Core.Symbolic (Query, QueryContext, QueryState, State,
                               SMTModel, SMTResult, SW)

import qualified Data.SBV.Control.Query as Trans
import qualified Data.SBV.Control.Utils as Trans

-- Data.SBV.Control.Query

getInfo :: SMTInfoFlag -> Query SMTInfoResponse
getInfo = Trans.getInfo

getOption :: (a -> SMTOption) -> Query (Maybe SMTOption)
getOption = Trans.getOption

getUnknownReason :: Query SMTReasonUnknown
getUnknownReason = Trans.getUnknownReason

getSMTResult :: Query SMTResult
getSMTResult = Trans.getSMTResult

getLexicographicOptResults :: Query SMTResult
getLexicographicOptResults = Trans.getLexicographicOptResults

getIndependentOptResults :: [String] -> Query [(String, SMTResult)]
getIndependentOptResults = Trans.getIndependentOptResults

getParetoOptResults :: Maybe Int -> Query (Bool, [SMTResult])
getParetoOptResults = Trans.getParetoOptResults

getModel :: Query SMTModel
getModel = Trans.getModel

checkSatAssuming :: [SBool] -> Query CheckSatResult
checkSatAssuming = Trans.checkSatAssuming

checkSatAssumingWithUnsatisfiableSet :: [SBool] -> Query (CheckSatResult, Maybe [SBool])
checkSatAssumingWithUnsatisfiableSet = Trans.checkSatAssumingWithUnsatisfiableSet

getAssertionStackDepth :: Query Int
getAssertionStackDepth = Trans.getAssertionStackDepth

inNewAssertionStack :: Query a -> Query a
inNewAssertionStack = Trans.inNewAssertionStack

push :: Int -> Query ()
push = Trans.push

pop :: Int -> Query ()
pop = Trans.pop

caseSplit :: Bool -> [(String, SBool)] -> Query (Maybe (String, SMTResult))
caseSplit = Trans.caseSplit

resetAssertions :: Query ()
resetAssertions = Trans.resetAssertions

echo :: String -> Query ()
echo = Trans.echo

exit :: Query ()
exit = Trans.exit

getUnsatCore :: Query [String]
getUnsatCore = Trans.getUnsatCore

getProof :: Query String
getProof = Trans.getProof

getInterpolant :: [String] -> Query String
getInterpolant = Trans.getInterpolant

getAssertions :: Query [String]
getAssertions = Trans.getAssertions

getAssignment :: Query [(String, Bool)]
getAssignment = Trans.getAssignment

mkSMTResult :: [Assignment] -> Query SMTResult
mkSMTResult = Trans.mkSMTResult

-- Data.SBV.Control.Utils

io :: IO a -> Query a
io = Trans.io

modifyQueryState :: (QueryState -> QueryState) -> Query ()
modifyQueryState = Trans.modifyQueryState

inNewContext :: (State -> IO a) -> Query a
inNewContext = Trans.inNewContext

freshVar :: SymWord a => String -> Query (SBV a)
freshVar = Trans.freshVar

freshArray_ :: (SymArray array, HasKind a, HasKind b) => Maybe (SBV b) -> Query (array a b)
freshArray_ = Trans.freshArray_

freshArray :: (SymArray array, HasKind a, HasKind b) => String -> Maybe (SBV b) -> Query (array a b)
freshArray = Trans.freshArray

queryDebug :: [String] -> Query ()
queryDebug = Trans.queryDebug

ask :: String -> Query String
ask = Trans.ask

send :: Bool -> String -> Query ()
send = Trans.send

retrieveResponse :: String -> Maybe Int -> Query [String]
retrieveResponse = Trans.retrieveResponse

getValue :: (SMTValue a) => SBV a -> Query a
getValue = Trans.getValue

getUninterpretedValue :: (HasKind a) => SBV a -> Query String
getUninterpretedValue = Trans.getUninterpretedValue

getValueCW :: Maybe Int -> SW -> Query CW
getValueCW = Trans.getValueCW

checkSatUsing :: String -> Query CheckSatResult
checkSatUsing = Trans.checkSatUsing

getUnsatAssumptions :: [String] -> [(String, a)] -> Query [a]
getUnsatAssumptions = Trans.getUnsatAssumptions

timeout :: Int -> Query a -> Query a
timeout = Trans.timeout

unexpected :: String -> String -> String -> Maybe [String] -> String -> Maybe [String] -> Query a
unexpected = Trans.unexpected

executeQuery :: QueryContext -> Query a -> Symbolic a
executeQuery = Trans.executeQuery
