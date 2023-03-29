-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Provers.Boolector
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- The connection to the Boolector SMT solver
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Provers.Boolector(boolector) where

import Data.SBV.Core.Data
import Data.SBV.SMT.SMT

-- | The description of the Boolector SMT solver
-- The default executable is @\"boolector\"@, which must be in your path. You can use the @SBV_BOOLECTOR@ environment variable to point to the executable on your system.
-- You can use the @SBV_BOOLECTOR_OPTIONS@ environment variable to override the options.
boolector :: SMTSolver
boolector = SMTSolver {
           name         = Boolector
         , executable   = "boolector"
         , preprocess   = id
         , options      = const ["--smt2", "-m", "--output-format=smt2", "--no-exit-codes", "--incremental"]
         , engine       = standardEngine "SBV_BOOLECTOR" "SBV_BOOLECTOR_OPTIONS"
         , capabilities = SolverCapabilities {
                                supportsQuantifiers        = False
                              , supportsDefineFun          = True
                              , supportsDistinct           = True
                              , supportsBitVectors         = True
                              , supportsUninterpretedSorts = False
                              , supportsUnboundedInts      = False
                              , supportsInt2bv             = False
                              , supportsReals              = False
                              , supportsApproxReals        = False
                              , supportsDeltaSat           = Nothing
                              , supportsIEEE754            = False
                              , supportsSets               = False
                              , supportsOptimization       = False
                              , supportsPseudoBooleans     = False
                              , supportsCustomQueries      = True
                              , supportsGlobalDecls        = True
                              , supportsDataTypes          = False
                              , supportsFoldAndMap         = False
                              , supportsSpecialRels        = False
                              , supportsDirectAccessors    = False
                              , supportsFlattenedModels    = Nothing
                              }
         }
