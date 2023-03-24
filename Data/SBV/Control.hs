-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Control
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Control sublanguage for interacting with SMT solvers.
-----------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Control (
     -- $queryIntro

     -- * User queries
       ExtractIO(..), MonadQuery(..), Queriable(..), Fresh(..), Query, query

     -- * Create a fresh variable
     , freshVar_, freshVar

     -- * Create a fresh array
     , freshArray_, freshArray

     -- * Checking satisfiability
     , CheckSatResult(..), checkSat, ensureSat, checkSatUsing, checkSatAssuming, checkSatAssumingWithUnsatisfiableSet

     -- * Querying the solver
     -- ** Extracting values
     , getValue, registerUISMTFunction, getFunction, getUninterpretedValue, getModel, getAssignment, getSMTResult, getUnknownReason, getObservables

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

import Data.SBV.Core.Symbolic (MonadQuery(..), Query, Queriable(..), Fresh(..), Symbolic, QueryContext(..))

import Data.SBV.Control.BaseIO
import Data.SBV.Control.Query hiding (  getInfo, getOption, getUnknownReason, getObservables
                                      , getSMTResult, getLexicographicOptResults
                                      , getIndependentOptResults
                                      , getParetoOptResults, getModel
                                      , checkSatAssuming
                                      , checkSatAssumingWithUnsatisfiableSet
                                      , getAssertionStackDepth
                                      , inNewAssertionStack, push, pop
                                      , caseSplit, resetAssertions, echo, exit
                                      , getUnsatCore, getProof, getInterpolantMathSAT, getInterpolantZ3
                                      , getAbduct, getAbductNext
                                      , getAssertions, getAssignment
                                      , mkSMTResult, freshVar_, freshVar
                                      , freshArray, freshArray_, checkSat, ensureSat
                                      , checkSatUsing, getValue
                                      , getUninterpretedValue, timeout, io)
import Data.SBV.Control.Utils (registerUISMTFunction)

import Data.SBV.Utils.ExtractIO (ExtractIO(..))

import qualified Data.SBV.Control.Utils as Trans

-- | Run a custom query
query :: Query a -> Symbolic a
query = Trans.executeQuery QueryExternal

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
                      Unk    -> error "Solver said unknown!"
                      DSat{} -> error "Solver said DSat!"
                      Unsat  -> return Nothing -- no solution!
                      Sat    -> -- Query the values:
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
                                     Unk    -> error "Solver said unknown!"
                                     DSat{} -> error "Solver said DSat!"
                                     Unsat  -> return Nothing
                                     Sat    -> do xv2 <- getValue x
                                                  yv2 <- getValue y

                                                  return $ Just (xv2, yv2)
@

Note the type of @test@: it returns an optional pair of integers in the 'Symbolic' monad. We turn
it into an IO value with the 'Data.SBV.Control.runSMT' function: (There's also 'Data.SBV.Control.runSMTWith' that uses a user specified
solver instead of the default. Note that 'Data.SBV.Provers.z3' is best supported (and tested), if you use another solver your results may vary!)

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

  - "Documentation.SBV.Examples.Queries.AllSat": Simulating SBV's 'Data.SBV.allSat' using queries.
  - "Documentation.SBV.Examples.Queries.CaseSplit": Performing a case-split during a query.
  - "Documentation.SBV.Examples.Queries.Enums": Using enumerations in queries.
  - "Documentation.SBV.Examples.Queries.FourFours": Solution to a fun arithmetic puzzle, coded using queries.
  - "Documentation.SBV.Examples.Queries.GuessNumber": The famous number guessing game.
  - "Documentation.SBV.Examples.Queries.UnsatCore": Extracting unsat-cores using queries.
  - "Documentation.SBV.Examples.Queries.Interpolants": Extracting interpolants using queries.
-}
