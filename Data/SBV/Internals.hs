---------------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Internals
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Low level functions to access the SBV infrastructure, for developers who
-- want to build further tools on top of SBV. End-users of the library
-- should not need to use this module.
---------------------------------------------------------------------------------

module Data.SBV.Internals (
  -- * Running symbolic programs /manually/
    Result(..), SBVRunMode(..)

  -- * Solver capabilities
  , SolverCapabilities(..)

  -- * Internal structures useful for low-level programming
  , module Data.SBV.Core.Data

  -- * Operations useful for instantiating SBV type classes
  , genLiteral, genFromCW, CW(..), genMkSymVar, checkAndConvert, genParse, showModel, SMTModel(..), liftQRem, liftDMod

  -- * Getting SMT-Lib output (for offline analysis)
  , compileToSMTLib, generateSMTBenchmarks

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
  , sendStringToSolver, sendRequestToSolver, retrieveStringFromSolver, synchronizeSolverComms

  ) where

import Control.Monad (unless)

import Data.SBV.Core.Data
import Data.SBV.Core.Model      (genLiteral, genFromCW, genMkSymVar, liftQRem, liftDMod)
import Data.SBV.Core.Splittable (checkAndConvert)

import Data.SBV.Compilers.C       (compileToC', compileToCLib')
import Data.SBV.Compilers.CodeGen

import Data.SBV.Provers.Prover (compileToSMTLib, generateSMTBenchmarks)

import Data.SBV.SMT.SMT (genParse, showModel)

import Data.SBV.Utils.Numeric

import Data.SBV.Utils.TDiff
import Data.SBV.Utils.PrettyNum

import Data.Time (getZonedTime)

import qualified Data.SBV.Control.Utils as Query

-- | Send an arbitrary string to the solver in a query.
-- Note that this is inherently dangerous as it can put the solver in an arbitrary
-- state and confuse SBV. If you use this feature, you are on your own!
sendStringToSolver :: String -> Query ()
sendStringToSolver = Query.send False

-- | Retrieve a full line from the solver, with an optional timeout in milliseconds.
-- If the time-out is exceeded, then we will raise an error. Note that this is inherently
-- dangerous as it can put the solver in an arbitrary state and confuse SBV. If you use this
-- feature, you are on your own!
retrieveStringFromSolver :: Maybe Int -> Query String
retrieveStringFromSolver = Query.retrieveString

-- | Send an arbitrary string to the solver in a query, and return a response.
-- Note that this is inherently dangerous as it can put the solver in an arbitrary
-- state and confuse SBV.
sendRequestToSolver :: String -> Query String
sendRequestToSolver = Query.ask

-- | Synchronize communications with the solver. In normal operation, you should not need
-- this functionality. In rare circumstances, however, the solver/SBV communication might
-- go out of sync. Please report if this happens regularly for good reason. In exceptional
-- cases, you can use this function to make sure the solver is synchronized with SBV. If the
-- optional timeout value (in milliseconds) is exceeded, we'll raise an error.
synchronizeSolverComms :: Maybe Int -> Query ()
synchronizeSolverComms mbTo = do ts  <- Query.io (show <$> getZonedTime)
                                 let tag = show $ "SBV Synchronization point at " ++ ts
                                     cmd = "(echo " ++ tag ++ ")"

                                 sendStringToSolver cmd

                                 Query.queryDebug ["** Attempting to synchronize with tag: " ++ tag]

                                 let loop = do s <- retrieveStringFromSolver mbTo
                                               unless (s == tag) $  do Query.queryDebug ["*** Synchronization loop, ignoring response: " ++ s]
                                                                       loop

                                 loop

                                 Query.queryDebug ["** Synchronization point reached!"]

{- $coordinateSolverInfo
In rare cases it might be necessary to send an arbitrary string down to the solver. Needless to say, this
should be avoided if at all possible. Users should prefer the provided API. If you do find yourself
needing 'send' and 'ask' directly, please get in touch to see if SBV can support a typed API for your use case.
Similarly, the function 'synchronizeSolverComms' might occasionally be necessary to clean-up the communication
buffer. We would like to hear if you do need these functions regularly so we can provide better support.
-}

{-# ANN module ("HLint: ignore Use import/export shortcut" :: String) #-}
