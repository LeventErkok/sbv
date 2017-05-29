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
     -- * Adding new assertions
       assert, namedAssert

     -- * Sending an arbitrary string
     , send, ask

     -- * Checking satisfiability
     , CheckSatResult(..), checkSat

     -- * Extracting values
     , getValue, getModel

     -- * Controlling the solver behavior
     , SMTOption(..), setOption
     , ignoreExitCode

     -- * Extracting the unsat core
     , getUnsatCore

     -- * Getting solver information
     , SMTInfoFlag(..), SMTErrorBehavior(..), SMTReasonUnknown(..), SMTInfoResponse(..)
     , getInfo

     -- * Constructing assignments
     , (|->)

     -- * Entering and exiting assertion stack
     , getAssertionStackDepth, push, pop, reset

     -- * Terminating the query
     , sbvResume
     , result
     , success
     , failure

     -- * Performing actions
     , io

     -- * Logics supported
     , Logic(..)

     ) where

import Data.SBV.Control.Query
