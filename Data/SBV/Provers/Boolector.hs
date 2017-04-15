-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.Boolector
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- The connection to the Boolector SMT solver
-----------------------------------------------------------------------------

module Data.SBV.Provers.Boolector(boolector) where

import Data.SBV.Core.Data
import Data.SBV.SMT.SMT

-- | The description of the Boolector SMT solver
-- The default executable is @\"boolector\"@, which must be in your path. You can use the @SBV_BOOLECTOR@ environment variable to point to the executable on your system.
-- The default options are @\"-m --smt2\"@. You can use the @SBV_BOOLECTOR_OPTIONS@ environment variable to override the options.
boolector :: SMTSolver
boolector = SMTSolver {
           name         = Boolector
         , executable   = "boolector"
         , options      = ["--smt2", "--smt2-model", "--no-exit-codes"]
         , engine       = standardEngine "SBV_BOOLECTOR" "SBV_BOOLECTOR_OPTIONS" addTimeOut standardModel
         , capabilities = SolverCapabilities {
                                capSolverName              = "Boolector"
                              , mbDefaultLogic             = const Nothing
                              , supportsMacros             = False
                              , supportsProduceModels      = True
                              , supportsQuantifiers        = False
                              , supportsUninterpretedSorts = False
                              , supportsUnboundedInts      = False
                              , supportsReals              = False
                              , supportsFloats             = False
                              , supportsDoubles            = False
                              , supportsOptimization       = False
                              }
         }
 where addTimeOut o i | i < 0 = error $ "Boolector: Timeout value must be non-negative, received: " ++ show i
                      | True  = o ++ ["-t=" ++ show i]
