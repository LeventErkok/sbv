-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Internals
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Low level functions to access the SBV infrastructure, for developers who
-- want to build further tools on top of SBV. End-users of the library
-- should not need to use this module.
--
-- NB. There are various coding invariants in SBV that are maintained
-- throughout the code. Indiscriminate use of functions in this module
-- can break those invariants. So, you are on your own if you do utilize
-- the functions here. (Unfortunately, what exactly those invariants are
-- is a very good but also a very difficult question to answer!)
-----------------------------------------------------------------------------

module Data.SBV.Internals (
  -- * Running symbolic programs /manually/
    Result(..), SBVRunMode(..), IStage(..), QueryContext(..)

  -- * Solver capabilities
  , SolverCapabilities(..)

  -- * Internal structures useful for low-level programming
  , module Data.SBV.Core.Data

  -- * Operations useful for instantiating SBV type classes
  , genLiteral, genFromCV, CV(..), genMkSymVar, genParse, showModel, SMTModel(..), liftQRem, liftDMod, registerKind

  -- * Compilation to C, extras
  , compileToC', compileToCLib'

  -- * Code generation primitives
  , module Data.SBV.Compilers.CodeGen

  -- * Various math utilities around floats
  , module Data.SBV.Utils.Numeric

  -- * Pretty number printing
  , module Data.SBV.Utils.PrettyNum

  -- * Timing computations
  , module Data.SBV.Utils.TDiff

  -- * Coordinating with the solver
  -- $coordinateSolverInfo
  , sendStringToSolver, sendRequestToSolver, retrieveResponseFromSolver

  -- * Defining new metrics
  , addSValOptGoal, sFloatAsComparableSWord32, sDoubleAsComparableSWord64
  ) where

import Control.Monad.IO.Class (MonadIO)

import Data.SBV.Core.Data
import Data.SBV.Core.Model      (genLiteral, genFromCV, genMkSymVar, liftQRem, liftDMod)
import Data.SBV.Core.Symbolic   (IStage(..), QueryContext(..), MonadQuery, addSValOptGoal, registerKind)

import Data.SBV.Core.Floating   (sFloatAsComparableSWord32, sDoubleAsComparableSWord64)

import Data.SBV.Compilers.C       (compileToC', compileToCLib')
import Data.SBV.Compilers.CodeGen

import Data.SBV.SMT.SMT (genParse, showModel)

import Data.SBV.Utils.Numeric

import Data.SBV.Utils.TDiff
import Data.SBV.Utils.PrettyNum

import qualified Data.SBV.Control.Utils as Query

-- | Send an arbitrary string to the solver in a query.
-- Note that this is inherently dangerous as it can put the solver in an arbitrary
-- state and confuse SBV. If you use this feature, you are on your own!
sendStringToSolver :: (MonadIO m, MonadQuery m) => String -> m ()
sendStringToSolver = Query.send False

-- | Retrieve multiple responses from the solver, until it responds with a user given
-- tag that we shall arrange for internally. The optional timeout is in milliseconds.
-- If the time-out is exceeded, then we will raise an error. Note that this is inherently
-- dangerous as it can put the solver in an arbitrary state and confuse SBV. If you use this
-- feature, you are on your own!
retrieveResponseFromSolver :: (MonadIO m, MonadQuery m) => String -> Maybe Int -> m [String]
retrieveResponseFromSolver = Query.retrieveResponse

-- | Send an arbitrary string to the solver in a query, and return a response.
-- Note that this is inherently dangerous as it can put the solver in an arbitrary
-- state and confuse SBV.
sendRequestToSolver :: (MonadIO m, MonadQuery m) => String -> m String
sendRequestToSolver = Query.ask

{- $coordinateSolverInfo
In rare cases it might be necessary to send an arbitrary string down to the solver. Needless to say, this
should be avoided if at all possible. Users should prefer the provided API. If you do find yourself
needing 'Data.SBV.Control.Utils.send' and 'Data.SBV.Control.Utils.ask' directly, please get in touch to see if SBV can support a typed API for your use case.
Similarly, the function 'retrieveResponseFromSolver' might occasionally be necessary to clean-up the communication
buffer. We would like to hear if you do need these functions regularly so we can provide better support.
-}

{-# ANN module ("HLint: ignore Use import/export shortcut" :: String) #-}
