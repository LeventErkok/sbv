-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Control
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Control sublanguage for interacting with SMT solvers, see the 'QueryUsing'
-- tactic for details.
-----------------------------------------------------------------------------

{-# LANGUAGE NamedFieldPuns #-}

module Data.SBV.Control(
     -- * Communicating with the solver
       getConfig, ask

     -- * Performing actions
     , io

     -- * Add new assertions
     , assert

     -- * Terminating the query
     , continue
     , result
     , failure
     ) where

import Control.Monad.State.Lazy (get)
import Control.Monad.Trans      (liftIO)

import Data.SBV.Core.Data

import Data.SBV.Core.Symbolic (QueryState(..), QueryContext, Query(..), SMTResult(..), SMTConfig(..), withNewIncState, IncState)

-- | Get the current configuration
getConfig :: Query SMTConfig
getConfig = queryConfig <$> get

-- | Get the current context
getContext :: Query QueryContext
getContext = queryContext <$> get

-- | Send a string to the solver, and return the response
ask :: String -> Query String
ask s = do QueryState{queryAsk, queryConfig} <- get

           let dbg what m
                 | verbose queryConfig = message $ what ++ " " ++ m
                 | True                = return ()

           dbg "-->" s
           r <- io $ queryAsk s
           dbg "<--" r

           return r

-- | Send a string to the solver, where no answer is expected
send :: String -> Query ()
send s = do QueryState{querySend, queryConfig} <- get

            let dbg what m
                  | verbose queryConfig = message $ what ++ " " ++ m
                  | True                = return ()

            dbg "-->" s
            io $ querySend s

-- | Perform an IO action
io :: IO a -> Query a
io = liftIO

-- | Print a message on the console
message :: String -> Query ()
message = io . putStrLn

-- | Run what SBV would've run, should we not have taken control
continue :: Query [SMTResult]
continue = do QueryState{queryDefault} <- get
              io queryDefault

-- | Sync-up the external solver with new context we have generated
syncUpSolver :: IncState -> Query ()
syncUpSolver _ = return ()

-- | Execute in a new incremental context
inNewContext :: (State -> IO a) -> Query a
inNewContext act = do st <- getContext
                      (is, r) <- io $ withNewIncState st act
                      syncUpSolver is
                      return r

-- | Assert a new "fact"
assert :: SBool -> Query ()
assert s = do sw <- inNewContext (`sbvToSW` s)
              send $ "(assert " ++ show sw ++ ")"

-- | Produce this answer as the result
result :: SMTResult -> Query [SMTResult]
result x = return [x]

-- | Fail with error
failure :: [String] -> Query [SMTResult]
failure ms = do QueryState{queryConfig} <- get
                result $ ProofError queryConfig ms
