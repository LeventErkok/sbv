-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Provers.MathSAT
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- The connection to the MathSAT SMT solver
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Provers.MathSAT(mathSAT) where

import Data.SBV.Core.Data
import Data.SBV.SMT.SMT

import Data.SBV.Control.Types

-- | The description of the MathSAT SMT solver
-- The default executable is @\"mathsat\"@, which must be in your path. You can use the @SBV_MATHSAT@ environment variable to point to the executable on your system.
-- The default options are @\"-input=smt2\"@. You can use the @SBV_MATHSAT_OPTIONS@ environment variable to override the options.
mathSAT :: SMTSolver
mathSAT = SMTSolver {
           name         = MathSAT
         , executable   = "mathsat"
         , preprocess   = id
         , options      = modConfig ["-input=smt2", "-theory.fp.minmax_zero_mode=4"]
         , engine       = standardEngine "SBV_MATHSAT" "SBV_MATHSAT_OPTIONS"
         , capabilities = SolverCapabilities {
                                supportsQuantifiers        = True
                              , supportsUninterpretedSorts = True
                              , supportsUnboundedInts      = True
                              , supportsReals              = True
                              , supportsApproxReals        = False
                              , supportsIEEE754            = True
                              , supportsOptimization       = False
                              , supportsPseudoBooleans     = False
                              , supportsCustomQueries      = True
                              , supportsGlobalDecls        = False
                              , supportsFlattenedSequences = Nothing
                              }
         }

 where -- If unsat cores are needed, MathSAT requires an explicit command-line argument
       modConfig :: [String] -> SMTConfig -> [String]
       modConfig opts cfg
        | or [b | ProduceUnsatCores b <- solverSetOptions cfg]
        = opts ++ ["-unsat_core_generation=3"]
        | True
        = opts
