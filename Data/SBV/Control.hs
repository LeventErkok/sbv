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

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Control (
     -- $queryIntro

     -- * User queries
       ExtractIO(..), MonadQuery(..), Queriable(..), Query, query

     -- * Create a fresh variable
     , freshVar_, freshVar

     -- * Checking satisfiability
     , CheckSatResult(..), checkSat, ensureSat, checkSatUsing, checkSatAssuming, checkSatAssumingWithUnsatisfiableSet

     -- * Querying the solver
     -- ** Extracting values
     , getValue, registerUISMTFunction, registerSMTType, getFunction, getUninterpretedValue, getModel, getAssignment, getSMTResult, getUnknownReason, getObservables

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

import Data.SBV.Core.Symbolic (Symbolic, QueryContext(..))

import Data.SBV.Trans.Control hiding (query)
import Data.SBV.Control.Utils (registerUISMTFunction, registerSMTType)

import qualified Data.SBV.Control.Utils as Trans

import Data.SBV.Core.Data (SymVal, SBV, literal)

import Control.Monad.Trans (MonadIO)
import Data.Kind (Type)


-- | Run a custom query
query :: Query a -> Symbolic a
query = Trans.executeQuery QueryExternal

-- | An queriable value: Mapping between concrete/symbolic values. If your type is traversable and simply embeds
-- symbolic equivalents for one type, then you can simply define 'create'. (Which is the most common case.)
class Queriable m a where
  type QueryResult a :: Type

  -- | ^ Create a new symbolic value of type @a@
  create  :: QueryT m a

  -- | ^ Extract the current value in a SAT context
  project :: a -> QueryT m (QueryResult a)

  -- | ^ Create a literal value. Morally, 'embed' and 'project' are inverses of each other
  -- via the 'QueryT' monad transformer.
  embed   :: QueryResult a -> QueryT m a

  default project :: (a ~ t (SBV e), QueryResult a ~ t e, Traversable t, MonadIO m, SymVal e) => a -> QueryT m (QueryResult a)
  project = mapM getValue

  default embed :: (a ~ t (SBV e), QueryResult a ~ t e, Traversable t, MonadIO m, SymVal e) => QueryResult a -> QueryT m a
  embed = pure . fmap literal
  {-# MINIMAL create #-}

-- | Generic 'Queriable' instance for 'SymVal' values
instance {-# OVERLAPPABLE #-} (MonadIO m, SymVal a) => Queriable m (SBV a) where
  type QueryResult (SBV a) = a

  create  = freshVar_
  project = getValue
  embed   = return . literal

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
