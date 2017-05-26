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
     -- * Add new assertions
       assert

     -- * Sending an arbitrary string
     , send, ask

     -- * Checking satisfiability
     , CheckSatResult(..), checkSat

     -- * Extracting values
     , getValue, getModel

     -- * Controlling the solver behavior
     , SMTOption(..), setOption
     , ignoreExitCode

     -- * Constructing an assignment for a model
     , (|->)

     -- * Terminating the query
     , sbvResume
     , result
     , success
     , failure

     -- * Performing actions
     , io
     ) where

import Data.SBV.Control.Query
