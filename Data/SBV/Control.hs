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

{-# LANGUAGE NamedFieldPuns #-}

module Data.SBV.Control(
     -- * Add new assertions
       assert

     -- * Sending an arbitrary string
     , ask

     -- * Controlling the solver behavior
     , ignoreExitCode

     -- * Terminating the query
     , continue
     , result
     , failure

     -- * Performing actions
     , io
     ) where

import Control.Monad.State.Lazy (get, modify)
import Control.Monad.Trans      (liftIO)

import Data.IORef (readIORef)
import Data.List  (sortBy)

import qualified Data.Map as Map (toList)

import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic (QueryState(..), Query(..), SMTResult(..), SMTConfig(..), withNewIncState, IncState(..))

import Data.SBV.SMT.SMTLib (toIncSMTLib2)

-- | Get the current configuration
getConfig :: Query SMTConfig
getConfig = queryConfig <$> get

-- | Get the current context
getContextState :: Query State
getContextState = contextState . queryContext <$> get

-- | Should we ignore the exit code from the solver upon finish?
-- The default is /not/ to ignore. However, you might want to set
-- this to 'False' before you issue a call to 'continue', in case the interactive
-- part of your query caused solver to issue some errors that you would
-- like to ignore.
ignoreExitCode :: Bool -> Query ()
ignoreExitCode b = modify (\qs -> qs {queryIgnoreExitCode  = b})

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

-- | Perform an arbitrary IO action.
io :: IO a -> Query a
io = liftIO

-- | Print a message on the console
message :: String -> Query ()
message = io . putStrLn

-- | Run what SBV would've run, should we not have taken control.
continue :: Query [SMTResult]
continue = do QueryState{queryDefault, queryIgnoreExitCode} <- get
              io $ queryDefault queryIgnoreExitCode

-- | Sync-up the external solver with new context we have generated
syncUpSolver :: IncState -> Query ()
syncUpSolver is = do
        cfg <- getConfig
        ls  <- io $ do let swapc ((_, a), b)   = (b, a)
                           cmp   (a, _) (b, _) = a `compare` b
                       cnsts <- (sortBy cmp . map swapc . Map.toList) `fmap` readIORef (rNewConsts is)
                       as    <- readIORef (rNewAsgns  is)
                       return $ toIncSMTLib2 cnsts as cfg
        mapM_ send ls

-- | Execute in a new incremental context
inNewContext :: (State -> IO a) -> Query a
inNewContext act = do st <- getContextState
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

{- $commIntro
Some good text here
-}
