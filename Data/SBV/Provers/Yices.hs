-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Provers.Yices
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- The connection to the Yices SMT solver
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Provers.Yices(yices) where

import Data.SBV.Core.Data
import Data.SBV.SMT.SMT

-- | The description of the Yices SMT solver
-- The default executable is @\"yices-smt2\"@, which must be in your path. You can use the @SBV_YICES@ environment variable to point to the executable on your system.
-- You can use the @SBV_YICES_OPTIONS@ environment variable to override the options.
yices :: SMTSolver
yices = SMTSolver {
           name         = Yices
         , executable   = "yices-smt2"
         , preprocess   = id
         , options      = const ["--incremental"]
         , engine       = standardEngine "SBV_YICES" "SBV_YICES_OPTIONS"
         , capabilities = SolverCapabilities {
                                supportsQuantifiers        = False
                              , supportsDefineFun          = True
                              , supportsDistinct           = True
                              , supportsBitVectors         = True
                              , supportsUninterpretedSorts = True
                              , supportsUnboundedInts      = True
                              , supportsInt2bv             = False
                              , supportsReals              = True
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
