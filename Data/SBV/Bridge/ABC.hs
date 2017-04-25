---------------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Bridge.ABC
-- Copyright   :  (c) Adam Foltzer
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Interface to the ABC verification and synthesis tool. Import this
-- module if you want to use ABC as your backend solver. Also see:
--
--       - "Data.SBV.Bridge.Boolector"
-- 
--       - "Data.SBV.Bridge.CVC4"
-- 
--       - "Data.SBV.Bridge.MathSAT"
-- 
--       - "Data.SBV.Bridge.Yices"
-- 
--       - "Data.SBV.Bridge.Z3"
--
---------------------------------------------------------------------------------

module Data.SBV.Bridge.ABC (
  -- * ABC specific interface
  sbvCurrentSolver
  -- ** Proving, checking satisfiability, optimization
  , prove, sat, allSat, safe, optimize, isVacuous, isTheorem, isSatisfiable
  -- * Non-Boolector specific SBV interface
  -- $moduleExportIntro
  , module Data.SBV
  ) where

import Data.SBV hiding (prove, sat, allSat, safe, optimize, isVacuous, isTheorem, isSatisfiable, sbvCurrentSolver)

-- | Current solver instance, pointing to abc.
sbvCurrentSolver :: SMTConfig
sbvCurrentSolver = abc

-- | Prove theorems, using ABC
prove :: Provable a
      => a              -- ^ Property to check
      -> IO ThmResult   -- ^ Response from the SMT solver, containing the counter-example if found
prove = proveWith sbvCurrentSolver

-- | Find satisfying solutions, using ABC
sat :: Provable a
    => a                -- ^ Property to check
    -> IO SatResult     -- ^ Response of the SMT Solver, containing the model if found
sat = satWith sbvCurrentSolver

-- | Check all 'sAssert' calls are safe, using ABC
safe :: SExecutable a
    => a                -- ^ Program containing sAssert calls
    -> IO [SafeResult]
safe = safeWith sbvCurrentSolver

-- | Find all satisfying solutions, using ABC
allSat :: Provable a
       => a                -- ^ Property to check
       -> IO AllSatResult  -- ^ List of all satisfying models
allSat = allSatWith sbvCurrentSolver

-- | Optimize objectives, using ABC
optimize :: Provable a
         => a                -- ^ Program with objectives
         -> IO OptimizeResult
optimize = optimizeWith sbvCurrentSolver

-- | Check vacuity of the explicit constraints introduced by calls to the 'constrain' function, using ABC
isVacuous :: Provable a
          => a             -- ^ Property to check
          -> IO Bool       -- ^ True if the constraints are unsatisifiable
isVacuous = isVacuousWith sbvCurrentSolver

-- | Check if the statement is a theorem, with an optional time-out in seconds, using ABC
isTheorem :: Provable a
          => Maybe Int          -- ^ Optional time-out, specify in seconds
          -> a                  -- ^ Property to check
          -> IO (Maybe Bool)    -- ^ Returns Nothing if time-out expires
isTheorem = isTheoremWith sbvCurrentSolver

-- | Check if the statement is satisfiable, with an optional time-out in seconds, using ABC
isSatisfiable :: Provable a
              => Maybe Int       -- ^ Optional time-out, specify in seconds
              -> a               -- ^ Property to check
              -> IO (Maybe Bool) -- ^ Returns Nothing if time-out expiers
isSatisfiable = isSatisfiableWith sbvCurrentSolver

{- $moduleExportIntro
The remainder of the SBV library that is common to all back-end SMT solvers, directly coming from the "Data.SBV" module.
-}
