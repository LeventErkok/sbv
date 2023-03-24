-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Trans.Control
-- Copyright : (c) Brian Schroeder
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- More generalized alternative to @Data.SBV.Control@ for advanced client use
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Trans.Control (

     -- * User queries
       ExtractIO(..), MonadQuery(..), QueryT, Query, query

     -- * Create a fresh variable
     , freshVar_, freshVar

     -- * Create a fresh array
     , freshArray_, freshArray, freshLambdaArray_, freshLambdaArray

     -- * Checking satisfiability
     , CheckSatResult(..), checkSat, ensureSat, checkSatUsing, checkSatAssuming, checkSatAssumingWithUnsatisfiableSet

     -- * Querying the solver
     -- ** Extracting values
     , getValue, getFunction, getUninterpretedValue, getModel, getAssignment, getSMTResult, getUnknownReason, getObservables

     -- ** Extracting the unsat core
     , getUnsatCore

     -- ** Extracting a proof
     , getProof

     -- ** Extracting interpolants
     , getInterpolantMathSAT, getInterpolantZ3

     -- ** Getting abducts
     , getAbduct, getAbductNext

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

import Data.SBV.Core.Symbolic (MonadQuery(..), QueryT, Query, SymbolicT, QueryContext(..))

import Data.SBV.Control.Query
import Data.SBV.Control.Utils (queryDebug, executeQuery, getFunction)

import Data.SBV.Utils.ExtractIO

-- | Run a custom query.
query :: ExtractIO m => QueryT m a -> SymbolicT m a
query = executeQuery QueryExternal
