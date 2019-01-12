-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Trans.Control
-- Author    : Brian Schroeder, Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- More generalized alternative to @Data.SBV.Control@ for advanced client use
-----------------------------------------------------------------------------

module Data.SBV.Trans.Control (

     -- * User queries
       ExtractIO(..), MonadQuery(..), QueryT, Query, query

     -- * Create a fresh variable
     , freshVar_, freshVar

     -- * Create a fresh array
     , freshArray_, freshArray

     -- * Checking satisfiability
     , CheckSatResult(..), checkSat, ensureSat, checkSatUsing, checkSatAssuming, checkSatAssumingWithUnsatisfiableSet

     -- * Querying the solver
     -- ** Extracting values
     , SMTValue(..), getValue, getUninterpretedValue, getModel, getAssignment, getSMTResult, getUnknownReason, getObservables

     -- ** Extracting the unsat core
     , getUnsatCore

     -- ** Extracting a proof
     , getProof

     -- ** Extracting interpolants
     , getInterpolant

     -- ** Extracting assertions
     , getAssertions

     -- * Getting solver information
     , SMTInfoFlag(..), SMTErrorBehavior(..), SMTInfoResponse(..)
     , getInfo, getOption

     -- * Entering and exiting assertion stack
     , getAssertionStackDepth, push, pop, inNewAssertionStack

     -- * Higher level tactics
     , caseSplit

     -- * Resetting the solver state
     , resetAssertions

     -- * Constructing assignments
     , (|->)

     -- * Terminating the query
     , mkSMTResult
     , exit

     -- * Controlling the solver behavior
     , ignoreExitCode, timeout

     -- * Miscellaneous
     , queryDebug
     , echo
     , io

     -- * Solver options
     , SMTOption(..)
     ) where

import Data.SBV.Core.Data     (SMTConfig(..))
import Data.SBV.Core.Symbolic (MonadQuery(..), QueryT, Query, SymbolicT, QueryContext(..))

import Data.SBV.Control.Query
import Data.SBV.Control.Utils (SMTValue(..), queryDebug, executeQuery)

import Data.SBV.Utils.ExtractIO

-- | Run a custom query.
query :: ExtractIO m => QueryT m a -> SymbolicT m a
query = executeQuery QueryExternal
