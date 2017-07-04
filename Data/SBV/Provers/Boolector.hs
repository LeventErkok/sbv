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
         , options      = const ["--smt2", "--smt2-model", "--no-exit-codes", "--incremental"]
         , engine       = standardEngine "SBV_BOOLECTOR" "SBV_BOOLECTOR_OPTIONS"
         , capabilities = SolverCapabilities {
                                supportsQuantifiers        = False
                              , supportsUninterpretedSorts = False
                              , supportsUnboundedInts      = False
                              , supportsReals              = False
                              , supportsApproxReals        = False
                              , supportsIEEE754            = False
                              , supportsOptimization       = False
                              , supportsPseudoBooleans     = False
                              , supportsCustomQueries      = True
                              , supportsGlobalDecls        = False
                              }
         }
