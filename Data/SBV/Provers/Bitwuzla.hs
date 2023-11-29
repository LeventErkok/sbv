-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Provers.Bitwuzla
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- The connection to the Bitwuzla SMT solver
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Provers.Bitwuzla(bitwuzla) where

import Data.SBV.Core.Data
import Data.SBV.SMT.SMT

-- | The description of the Bitwuzla SMT solver
-- The default executable is @\"bitwuzla\"@, which must be in your path. You can use the @SBV_BITWUZLA@ environment variable to point to the executable on your system.
-- You can use the @SBV_BITWUZLA_OPTIONS@ environment variable to override the options.
bitwuzla :: SMTSolver
bitwuzla = SMTSolver {
           name         = Bitwuzla
         , executable   = "bitwuzla"
         , preprocess   = id
         , options      = const ["--produce-models"]
         , engine       = standardEngine "SBV_BITWUZLA" "SBV_BITWUZLA_OPTIONS"
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
