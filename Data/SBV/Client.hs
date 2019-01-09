-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Client
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Cross-cutting toplevel client functions
-----------------------------------------------------------------------------

{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}

module Data.SBV.Client
  ( sbvCheckSolverInstallation
  , defaultSolverConfig
  , sbvAvailableSolvers
  , mkSymbolicEnumeration
  ) where

import Control.Monad (filterM)
import Data.Generics

import qualified Control.Exception   as C
import qualified Language.Haskell.TH as TH

import Data.SBV.Core.Data
import Data.SBV.Core.Model
import Data.SBV.Control.Utils
import Data.SBV.Provers.Prover

-- | Check whether the given solver is installed and is ready to go. This call does a
-- simple call to the solver to ensure all is well.
sbvCheckSolverInstallation :: SMTConfig -> IO Bool
sbvCheckSolverInstallation cfg = check `C.catch` (\(_ :: C.SomeException) -> return False)
  where check = do ThmResult r <- proveWith cfg $ \x -> (x+x) .== ((x*2) :: SWord8)
                   case r of
                     Unsatisfiable{} -> return True
                     _               -> return False

-- | The default configs corresponding to supported SMT solvers
defaultSolverConfig :: Solver -> SMTConfig
defaultSolverConfig Z3        = z3
defaultSolverConfig Yices     = yices
defaultSolverConfig Boolector = boolector
defaultSolverConfig CVC4      = cvc4
defaultSolverConfig MathSAT   = mathSAT
defaultSolverConfig ABC       = abc

-- | Return the known available solver configs, installed on your machine.
sbvAvailableSolvers :: IO [SMTConfig]
sbvAvailableSolvers = filterM sbvCheckSolverInstallation (map defaultSolverConfig [minBound .. maxBound])

-- | Make an enumeration a symbolic type.
mkSymbolicEnumeration :: TH.Name -> TH.Q [TH.Dec]
mkSymbolicEnumeration typeName = do
    let typeCon = TH.conT typeName
    [d| deriving instance Eq       $(typeCon)
        deriving instance Show     $(typeCon)
        deriving instance Ord      $(typeCon)
        deriving instance Read     $(typeCon)
        deriving instance Data     $(typeCon)
        deriving instance SymVal   $(typeCon)
        deriving instance HasKind  $(typeCon)
        deriving instance SMTValue $(typeCon)
        deriving instance SatModel $(typeCon)
      |]
