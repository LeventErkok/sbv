-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Provers.DReal
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- The connection to the dReal SMT solver
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Provers.DReal(dReal) where

import Data.SBV.Core.Data
import Data.SBV.SMT.SMT

-- | The description of the dReal SMT solver
-- The default executable is @\"dReal\"@, which must be in your path. You can use the @SBV_DREAL@ environment variable to point to the executable on your system.
-- You can use the @SBV_DREAL_OPTIONS@ environment variable to override the options.
dReal :: SMTSolver
dReal = SMTSolver {
           name         = DReal
         , executable   = "dReal"
         , preprocess   = id
         , options      = const ["--in", "--format", "smt2", "--smtlib2-compliant"]
         , engine       = standardEngine "SBV_DREAL" "SBV_DREAL_OPTIONS"
         , capabilities = SolverCapabilities {
                                supportsQuantifiers        = True     -- TBD
                              , supportsDefineFun          = False
                              , supportsUninterpretedSorts = True     -- TBD
                              , supportsUnboundedInts      = True     -- TBD
                              , supportsReals              = True     -- TBD
                              , supportsApproxReals        = True     -- TBD
                              , supportsIEEE754            = True     -- TBD
                              , supportsSets               = True     -- TBD
                              , supportsOptimization       = True     -- TBD
                              , supportsPseudoBooleans     = True     -- TBD
                              , supportsCustomQueries      = False
                              , supportsGlobalDecls        = True     -- TBD
                              , supportsDataTypes          = True     -- TBD
                              , supportsFlattenedModels    = Nothing  -- TBD
                              }
         }
