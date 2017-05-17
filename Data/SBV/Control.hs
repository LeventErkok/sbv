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
     , io, message

     -- * Terminating the query
     , continue
     , result
     , failure
     ) where

import Control.Monad.State.Lazy (get)
import Control.Monad.Trans      (liftIO)

import Data.SBV.Core.Symbolic (QueryState(..), Query(..), SMTResult(..), SMTConfig(..))

-- | Get the current configuration
getConfig :: Query SMTConfig
getConfig = do QueryState{queryConfig} <- get
               return queryConfig

-- | Send a string to the solver, and return the response
ask :: String -> Query String
ask s = do QueryState{queryAsk} <- get
           io $ queryAsk s

-- | Perform an IO action
io :: IO a -> Query a
io = liftIO

-- | Print a message on the console
message :: String -> Query ()
message = io . putStrLn

-- | Run what SBV would've run, should we not have taken control
continue :: Query [SMTResult]
continue = do QueryState{queryDefault} <- get
              io $ queryDefault

-- | Produce this answer as the result
result :: SMTResult -> Query [SMTResult]
result x = return [x]

-- | Fail with error
failure :: [String] -> Query [SMTResult]
failure ms = do QueryState{queryConfig} <- get
                result $ ProofError queryConfig ms
