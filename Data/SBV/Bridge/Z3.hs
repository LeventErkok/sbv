---------------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Bridge.Z3
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Interface to the Z3 SMT solver.
---------------------------------------------------------------------------------

module Data.SBV.Bridge.Z3 (
  -- * SBV interface using the Z3 SMT solver
  prove, sat, allSat, isVacuous, isTheorem, isSatisfiable, optimize, minimize, maximize
  -- * Module export, everything else in SBV
  , module Data.SBV
  ) where

import Data.SBV hiding (prove, sat, allSat, isVacuous, isTheorem, isSatisfiable, optimize, minimize, maximize)

-- | Prove theorems, using the Z3 SMT solver
prove :: Provable a => a -> IO ThmResult
prove = proveWith z3

-- | Find satisfying solutions, using the Z3 SMT solver
sat :: Provable a => a -> IO SatResult
sat = satWith z3

-- | Find all satisfying solutions, using the Z3 SMT solver
allSat :: Provable a => a -> IO AllSatResult
allSat = allSatWith z3

-- | Check vacuity, using the Z3 SMT solver
isVacuous :: Provable a => a -> IO Bool
isVacuous = isVacuousWith z3

-- | Check if the statement is a theorem, with an optional time-out in seconds, using the Z3 SMT solver
isTheorem :: Provable a => Maybe Int -> a -> IO (Maybe Bool)
isTheorem = isTheoremWith z3

-- | Check if the statement is satisfiable, with an optional time-out in seconds, using the Z3 SMT solver
isSatisfiable :: Provable a => Maybe Int -> a -> IO (Maybe Bool)
isSatisfiable = isSatisfiableWith z3

-- | Optimize cost functions, using the Z3 SMT solver
optimize :: (SatModel a, SymWord a, Show a, SymWord c, Show c) => OptimizeOpts -> (SBV c -> SBV c -> SBool) -> ([SBV a] -> SBV c) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
optimize = optimizeWith z3

-- | Minimize cost functions, using the Z3 SMT solver
minimize :: (SatModel a, SymWord a, Show a, SymWord c, Show c) => OptimizeOpts -> ([SBV a] -> SBV c) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
minimize = minimizeWith z3

-- | Maximize cost functions, using the Z3 SMT solver
maximize :: (SatModel a, SymWord a, Show a, SymWord c, Show c) => OptimizeOpts -> ([SBV a] -> SBV c) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
maximize = maximizeWith z3
