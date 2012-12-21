---------------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Bridge.CVC4
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Interface to the CVC4 SMT solver.
---------------------------------------------------------------------------------

module Data.SBV.Bridge.CVC4 (
  -- * SBV interface using the CVC4 SMT solver
  prove, sat, allSat, isVacuous, isTheorem, isSatisfiable, optimize, minimize, maximize
  -- * Module export, everything else in SBV
  , module Data.SBV
  ) where

import Data.SBV hiding (prove, sat, allSat, isVacuous, isTheorem, isSatisfiable, optimize, minimize, maximize)

-- | Prove theorems, using the CVC4 SMT solver
prove :: Provable a => a -> IO ThmResult
prove = proveWith cvc4

-- | Find satisfying solutions, using the CVC4 SMT solver
sat :: Provable a => a -> IO SatResult
sat = satWith cvc4

-- | Find all satisfying solutions, using the CVC4 SMT solver
allSat :: Provable a => a -> IO AllSatResult
allSat = allSatWith cvc4

-- | Check vacuity, using the CVC4 SMT solver
isVacuous :: Provable a => a -> IO Bool
isVacuous = isVacuousWith cvc4

-- | Check if the statement is a theorem, with an optional time-out in seconds, using the CVC4 SMT solver
isTheorem :: Provable a => Maybe Int -> a -> IO (Maybe Bool)
isTheorem = isTheoremWith cvc4

-- | Check if the statement is satisfiable, with an optional time-out in seconds, using the CVC4 SMT solver
isSatisfiable :: Provable a => Maybe Int -> a -> IO (Maybe Bool)
isSatisfiable = isSatisfiableWith cvc4

-- | Optimize cost functions, using the CVC4 SMT solver
optimize :: (SatModel a, SymWord a, Show a, SymWord c, Show c) => OptimizeOpts -> (SBV c -> SBV c -> SBool) -> ([SBV a] -> SBV c) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
optimize = optimizeWith cvc4

-- | Minimize cost functions, using the CVC4 SMT solver
minimize :: (SatModel a, SymWord a, Show a, SymWord c, Show c) => OptimizeOpts -> ([SBV a] -> SBV c) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
minimize = minimizeWith cvc4

-- | Maximize cost functions, using the CVC4 SMT solver
maximize :: (SatModel a, SymWord a, Show a, SymWord c, Show c) => OptimizeOpts -> ([SBV a] -> SBV c) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
maximize = maximizeWith cvc4
