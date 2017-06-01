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

     -- * Getting solver information
     , SMTInfoFlag(..), SMTErrorBehavior(..), SMTReasonUnknown(..), SMTInfoResponse(..)
     , getInfo


     -- * Entering and exiting assertion stack
     , getAssertionStackDepth, push, pop, reset

     -- * Communicating results back
     -- ** Constructing assignments
     , (|->)

     -- ** Terminating the query
     , sbvResume
     , result
     , success
     , failure

     -- * Controlling the solver behavior
     , SMTOption(..), setOption
     , ignoreExitCode

     -- * Performing actions
     , io

     -- * Sending an arbitrary string
     -- $sendStringInfo
     , send, ask

     -- * Logics supported
     , Logic(..)

     ) where

import Data.SBV.Control.Query

{- $sendStringInfo
In rare cases it might be necessary to send an arbitrary string down to the solver. Needless to say, this
should be avoided if at all possible. Users should prefer the provided API. If you do find yourself
needing 'send' and 'ask' directly, please get in touch to see if SBV can support a typed API for your use case.
-}
