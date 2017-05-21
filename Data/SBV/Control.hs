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

import Data.SBV.Core.Concrete (showCW)
import Data.SBV.Core.Symbolic (QueryState(..), QueryContext, Query(..), SMTResult(..), SMTConfig(..))

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

-- | Render a constant
renderCW :: CW -> [String]
renderCW cw = [showCW False cw]

-- | Render a node.
-- TODO: Handle the case when the node is a skolem constant.
-- But first, figure out precisely under which conditions
-- this is possible; we might want to reject some of those cases.
renderSW :: SW -> [String]
renderSW sw = [show sw]

-- | Render a symbolic value in state
render :: State -> SBV a -> IO [String]
render _  (SBV (SVal _ (Left cw))) = return $ renderCW cw
render st (SBV (SVal _ (Right f))) = renderSW <$> uncache f st

-- | Assert a new "fact"
assert :: SBool -> Query ()
assert s = do (st, _) <- getContext
              ls      <- io $ render st s

              let sendAll []     = return ()
                  sendAll [x]    = send $ "(assert " ++ x ++ ")" 
                  sendAll (x:xs) = send x >> sendAll xs

              sendAll ls

-- | Produce this answer as the result
result :: SMTResult -> Query [SMTResult]
result x = return [x]

-- | Fail with error
failure :: [String] -> Query [SMTResult]
failure ms = do QueryState{queryConfig} <- get
                result $ ProofError queryConfig ms
