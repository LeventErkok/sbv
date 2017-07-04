-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.MathSAT
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- The connection to the MathSAT SMT solver
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Provers.Z3(z3) where

import Data.Char (toLower)

import Data.SBV.Core.Data
import Data.SBV.SMT.SMT

import qualified System.Info as S(os)

-- Choose the correct prefix character for passing options
-- TBD: Is there a more foolproof way of determining this?
optionPrefix :: Char
optionPrefix
  | map toLower S.os `elem` ["linux", "darwin"] = '-'
  | True                                        = '/'   -- windows

-- | The description of the Z3 SMT solver.
-- The default executable is @\"z3\"@, which must be in your path. You can use the @SBV_Z3@ environment variable to point to the executable on your system.
-- The default options are @\"-nw -in -smt2\"@, which is valid for Z3 4.1. You can use the @SBV_Z3_OPTIONS@ environment variable to override the options.
z3 :: SMTSolver
z3 = SMTSolver {
           name         = Z3
         , executable   = "z3"
         , options      = map (optionPrefix:) . modConfig ["nw", "in", "smt2"]
         , engine       = standardEngine "SBV_Z3" "SBV_Z3_OPTIONS"
         , capabilities = SolverCapabilities {
                                supportsQuantifiers        = True
                              , supportsUninterpretedSorts = True
                              , supportsUnboundedInts      = True
                              , supportsReals              = True
                              , supportsApproxReals        = True
                              , supportsIEEE754            = True
                              , supportsOptimization       = True
                              , supportsPseudoBooleans     = True
                              , supportsCustomQueries      = True
                              , supportsGlobalDecls        = True
                              }
         }

 where modConfig :: [String] -> SMTConfig -> [String]
       modConfig opts _cfg = opts
