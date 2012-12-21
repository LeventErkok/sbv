---------------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Yices
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Interface to the Yices SMT solver.
---------------------------------------------------------------------------------

module Data.SBV.Yices (
  -- * SBV interface using the Yices SMT solver
  prove, sat, allSat, isVacuous, isTheorem, isSatisfiable, optimize, minimize, maximize
  -- * Module export, everything else in SBV
  , module Data.SBV
  ) where

import Data.SBV hiding (prove, sat, allSat, isVacuous, isTheorem, isSatisfiable, optimize, minimize, maximize)

-- | Prove theorems, using the Yices SMT solver
prove :: Provable a => a -> IO ThmResult
prove = proveWith yices

-- | Find satisfying solutions, using the Yices SMT solver
sat :: Provable a => a -> IO SatResult
sat = satWith yices

-- | Find all satisfying solutions, using the Yices SMT solver
allSat :: Provable a => a -> IO AllSatResult
allSat = allSatWith yices

-- | Check vacuity, using the Yices SMT solver
isVacuous :: Provable a => a -> IO Bool
isVacuous = isVacuousWith yices

-- | Check if the statement is a theorem, with an optional time-out in seconds, using the Yices SMT solver
isTheorem :: Provable a => Maybe Int -> a -> IO (Maybe Bool)
isTheorem = isTheoremWith yices

-- | Check if the statement is satisfiable, with an optional time-out in seconds, using the Yices SMT solver
isSatisfiable :: Provable a => Maybe Int -> a -> IO (Maybe Bool)
isSatisfiable = isSatisfiableWith yices

-- | Optimize cost functions, using the Yices SMT solver
optimize :: (SatModel a, SymWord a, Show a, SymWord c, Show c) => OptimizeOpts -> (SBV c -> SBV c -> SBool) -> ([SBV a] -> SBV c) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
optimize = optimizeWith yices

-- | Minimize cost functions, using the Yices SMT solver
minimize :: (SatModel a, SymWord a, Show a, SymWord c, Show c) => OptimizeOpts -> ([SBV a] -> SBV c) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
minimize = minimizeWith yices

-- | Maximize cost functions, using the Yices SMT solver
maximize :: (SatModel a, SymWord a, Show a, SymWord c, Show c) => OptimizeOpts -> ([SBV a] -> SBV c) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
maximize = maximizeWith yices
