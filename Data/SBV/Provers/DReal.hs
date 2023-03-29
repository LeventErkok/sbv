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

import Numeric

-- | The description of the dReal SMT solver
-- The default executable is @\"dReal\"@, which must be in your path. You can use the @SBV_DREAL@ environment variable to point to the executable on your system.
-- You can use the @SBV_DREAL_OPTIONS@ environment variable to override the options.
dReal :: SMTSolver
dReal = SMTSolver {
           name         = DReal
         , executable   = "dReal"
         , preprocess   = id
         , options      = modConfig ["--in", "--format", "smt2"]
         , engine       = standardEngine "SBV_DREAL" "SBV_DREAL_OPTIONS"
         , capabilities = SolverCapabilities {
                                supportsQuantifiers        = False
                              , supportsDefineFun          = True
                              , supportsDistinct           = False
                              , supportsBitVectors         = False
                              , supportsUninterpretedSorts = False
                              , supportsUnboundedInts      = True
                              , supportsInt2bv             = False
                              , supportsReals              = True
                              , supportsApproxReals        = False
                              , supportsDeltaSat           = Just "(get-option :precision)"
                              , supportsIEEE754            = False
                              , supportsSets               = False
                              , supportsOptimization       = False
                              , supportsPseudoBooleans     = False
                              , supportsCustomQueries      = False
                              , supportsGlobalDecls        = False
                              , supportsDataTypes          = False
                              , supportsFoldAndMap         = False
                              , supportsSpecialRels        = False
                              , supportsDirectAccessors    = False
                              , supportsFlattenedModels    = Nothing
                              }
         }
  where -- If dsat precision is given, pass that as an argument
       modConfig :: [String] -> SMTConfig -> [String]
       modConfig opts cfg = case dsatPrecision cfg of
                              Nothing -> opts
                              Just d  -> let sd = showFFloat Nothing d ""
                                         in if d > 0
                                            then opts ++ ["--precision", sd]
                                            else error $ unlines [ ""
                                                                 , "*** Data.SBV: Invalid precision to dReal: " ++ sd
                                                                 , "***           Precision must be non-negative."
                                                                 ]
