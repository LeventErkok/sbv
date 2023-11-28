-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Provers.OpenSMT
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- The connection to the OpenSMT SMT solver
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Provers.OpenSMT(openSMT) where

import Data.SBV.Core.Data
import Data.SBV.SMT.SMT

-- | The description of the OpenSMT SMT solver.
-- The default executable is @\"opensmt\"@, which must be in your path. You can use the @SBV_OpenSMT@ environment variable to point to the executable on your system.
-- You can use the @SBV_OpenSMT_OPTIONS@ environment variable to override the options.
openSMT :: SMTSolver
openSMT = SMTSolver {
           name         = OpenSMT
         , executable   = "openSMT"
         , preprocess   = id
         , options      = modConfig []
         , engine       = standardEngine "SBV_OpenSMT" "SBV_OpenSMT_OPTIONS"
         , capabilities = SolverCapabilities {
                                supportsQuantifiers        = False
                              , supportsDefineFun          = True
                              , supportsDistinct           = True
                              , supportsBitVectors         = False
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

 where modConfig :: [String] -> SMTConfig -> [String]
       modConfig opts _cfg = opts
