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

module Data.SBV.Control (
     -- $queryIntro

     -- * User queries
       Query, query

     -- * Create a fresh variable
     , freshVar_, freshVar

     -- * Checking satisfiability
     , CheckSatResult(..), checkSat, checkSatUsing, checkSatAssuming, checkSatAssumingWithUnsatisfiableSet

     -- * Querying the solver
     -- ** Extracting values
     , SMTValue(..), getValue, getUninterpretedValue, getModel, getAssignment, getSMTResult, getUnknownReason

     -- ** Extracting the unsat core
     , getUnsatCore

     -- ** Extracting a proof
     , getProof

     -- ** Extracting interpolants
     , getInterpolant

     -- ** Extracting assertions
     , getAssertions

     -- * Getting solver information
     , SMTInfoFlag(..), SMTErrorBehavior(..), SMTReasonUnknown(..), SMTInfoResponse(..)
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

     -- * Logics supported
     , Logic(..)

     ) where

import Data.SBV.Core.Data     (SMTProblem(..), SMTSolver(..), SMTConfig(..))
import Data.SBV.Core.Symbolic ( Query, IStage(..), SBVRunMode(..), Symbolic, Query(..), rSMTOptions
                              , extractSymbolicSimulationState, solverSetOptions, runMode
                              )

import Data.SBV.Control.Query
import Data.SBV.Control.Utils (runProofOn, SMTValue(..), queryDebug)

import Data.IORef (readIORef, writeIORef)

import qualified Control.Monad.Reader as R (ask)
import Control.Monad.Trans  (liftIO)
import Control.Monad.State  (evalStateT)

-- | Run a custom query
query :: Query a -> Symbolic a
query (Query userQuery) = do
     st <- R.ask
     rm <- liftIO $ readIORef (runMode st)
     case rm of
        -- Transitioning from setup
        SMTMode ISetup isSAT cfg -> liftIO $ do let backend = engine (solver cfg)

                                                res     <- extractSymbolicSimulationState st
                                                setOpts <- reverse <$> readIORef (rSMTOptions st)

                                                let SMTProblem{smtLibPgm} = runProofOn cfg isSAT [] res
                                                    cfg' = cfg { solverSetOptions = solverSetOptions cfg ++ setOpts }
                                                    pgm  = smtLibPgm cfg'

                                                writeIORef (runMode st) $ SMTMode IRun isSAT cfg

                                                backend cfg' st (show pgm) $ evalStateT userQuery

        -- Already in a query, in theory we can just continue, but that causes use-case issues
        -- so we reject it. TODO: Review if we should actually support this. The issue arises with
        -- expressions like this:
        --
        -- In the following t0's output doesn't get recorded, as the output call is too late when we get
        -- here. (The output field isn't "incremental.") So, t0/t1 behave differently!
        --
        --   t0 = satWith z3{verbose=True, transcript=Just "t.smt2"} $ query (return (false::SBool))
        --   t1 = satWith z3{verbose=True, transcript=Just "t.smt2"} $ ((return (false::SBool)) :: Predicate)
        --
        -- Also, not at all clear what it means to go in an out of query mode:
        --
        -- r = runSMTWith z3{verbose=True} $ do
        --         a' <- sInteger "a"
        --
        --        (a, av) <- query $ do _ <- checkSat
        --                              av <- getValue a'
        --                              return (a', av)
        --
        --        liftIO $ putStrLn $ "Got: " ++ show av
        --        -- constrain $ a .> literal av + 1      -- Cant' do this since we're "out" of query. Sigh.
        --
        --        bv <- query $ do constrain $ a .> literal av + 1
        --                         _ <- checkSat
        --                         getValue a
        --
        --        return $ a' .== a' + 1
        --
        -- This would be one possible implementation, alas it has the problems above:
        --
        --    SMTMode IRun _ _ -> liftIO $ evalStateT userQuery st
        --
        -- So, we just reject it.

        SMTMode IRun _ _ -> error $ unlines [ ""
                                            , "*** Data.SBV: Unsupported nested query is detected."
                                            , "***"
                                            , "*** Please group your queries into one block. Note that this"
                                            , "*** can also arise if you have a call to 'query' not within 'runSMT'"
                                            , "*** For instance, within 'sat'/'prove' calls with custom user queries."
                                            , "*** The solution is to do the sat/prove part in the query directly."
                                            , "***"
                                            , "*** While multiple/nested queries should not be necessary in general,"
                                            , "*** please do get in touch if your use case does require such a feature,"
                                            , "*** to see how we can accommodate such scenarios."
                                            ]

        -- Otherwise choke!
        m -> error $ unlines [ ""
                             , "*** Data.SBV: Invalid query call."
                             , "***"
                             , "***   Current mode: " ++ show m
                             , "***"
                             , "*** Query calls are only valid within runSMT/runSMTWith calls"
                             ]

{- $queryIntro
In certain cases, the user might want to take over the communication with the solver, programmatically
querying the engine and issuing commands accordingly. Queries can be extremely powerful as
they allow direct control of the solver. Here's a simple example:

@
    module Test where

    import Data.SBV
    import Data.SBV.Control  -- queries require this module to be imported!

    test :: Symbolic (Maybe (Integer, Integer))
    test = do x <- sInteger "x"   -- a free variable named "x"
              y <- sInteger "y"   -- a free variable named "y"

              -- require the sum to be 10
              constrain $ x + y .== 10

              -- Go into the Query mode
              query $ do
                    -- Query the solver: Are the constraints satisfiable?
                    cs <- checkSat
                    case cs of
                      Unk   -> error "Solver said unknown!"
                      Unsat -> return Nothing -- no solution!
                      Sat   -> -- Query the values:
                               do xv <- getValue x
                                  yv <- getValue y

                                  io $ putStrLn $ "Solver returned: " ++ show (xv, yv)

                                  -- We can now add new constraints,
                                  -- Or perform arbitrary computations and tell
                                  -- the solver anything we want!
                                  constrain $ x .> literal xv + literal yv

                                  -- call checkSat again
                                  csNew <- checkSat
                                  case csNew of
                                    Unk   -> error "Solver said unknown!"
                                    Unsat -> return Nothing
                                    Sat   -> do xv2 <- getValue x
                                                yv2 <- getValue y

                                                return $ Just (xv2, yv2)
@

Note the type of 'test', it returns an optional pair of integers in the 'Symbolic' monad. We turn
it into an IO value with the 'runSMT' function: (There's also 'runSMTWith' that uses a user specified
solver instead of the default.)

@
    pair :: IO (Maybe (Integer, Integer))
    pair = runSMT test
@

When run, this can return:

@
*Test> pair
Solver returned: (10,0)
Just (11,-1)
@

demonstrating that the user has full contact with the solver and can guide it as the program executes. SBV
provides access to many SMTLib features in the query mode, as exported from this very module.

For other examples see:

  - "Documentation.SBV.Examples.Queries.AllSat": Simulating SBV's 'allSat' using queries.
  - "Documentation.SBV.Examples.Queries.CaseSplit": Performing a case-split during a query.
  - "Documentation.SBV.Examples.Queries.Enums": Using enumerations in queries.
  - "Documentation.SBV.Examples.Queries.FourFours": Solution to a fun arithmetic puzzle, coded using queries.
  - "Documentation.SBV.Examples.Queries.GuessNumber": The famous number guessing game.
  - "Documentation.SBV.Examples.Queries.UnsatCore": Extracting unsat-cores using queries.
  - "Documentation.SBV.Examples.Queries.Interpolants": Extracting interpolants using queries.
-}
