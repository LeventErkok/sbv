-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Control
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Control sublanguage for interacting with SMT solvers.
-----------------------------------------------------------------------------

module Data.SBV.Control (
     -- * Checking satisfiability
       CheckSatResult(..), checkSat, checkSatAssuming

     -- * Querying the solver
     -- ** Extracting values
     , getValue, getModel

     -- ** Extracting the unsat core
     , getUnsatCore

     -- ** Extracting a proof
     , getProof

     -- ** Extracting assertions
     , getAssertions

     -- * Getting solver information
     , SMTInfoFlag(..), SMTErrorBehavior(..), SMTReasonUnknown(..), SMTInfoResponse(..)
     , getInfo


     -- * Entering and exiting assertion stack
     , getAssertionStackDepth, push, pop

     -- * Resetting the solver state
     , reset, resetAssertions

     -- * Communicating results back
     -- ** Constructing assignments
     , (|->)

     -- ** Terminating the query
     , sbvResume
     , result
     , success
     , failure
     , exit

     -- * Controlling the solver behavior
     , ignoreExitCode

     -- * Performing actions
     , io

     -- * Solver options
     , SMTOption(..)

     -- * Logics supported
     , Logic(..)

     ) where

import Data.SBV.Control.Query
