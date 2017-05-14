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

module Data.SBV.Provers.MathSAT(mathSAT) where

import Data.SBV.Core.Data
import Data.SBV.SMT.SMT

-- | The description of the MathSAT SMT solver
-- The default executable is @\"mathsat\"@, which must be in your path. You can use the @SBV_MATHSAT@ environment variable to point to the executable on your system.
-- The default options are @\"-input=smt2\"@. You can use the @SBV_MATHSAT_OPTIONS@ environment variable to override the options.
mathSAT :: SMTSolver
mathSAT = SMTSolver {
           name         = MathSAT
         , executable   = "mathsat"
         , options      = ["-input=smt2", "-theory.fp.minmax_zero_mode=4"]
         , engine       = standardEngine "SBV_MATHSAT" "SBV_MATHSAT_OPTIONS" modConfig addTimeOut standardModel
         , capabilities = SolverCapabilities {
                                capSolverName              = "MathSAT"
                              , mbDefaultLogic             = const Nothing
                              , supportsDefineFun          = True
                              , supportsProduceModels      = True
                              , supportsQuantifiers        = True
                              , supportsUninterpretedSorts = True
                              , supportsUnboundedInts      = True
                              , supportsReals              = True
                              , supportsFloats             = True
                              , supportsDoubles            = True
                              , supportsOptimization       = False
                              , supportsPseudoBooleans     = False
                              , supportsUnsatCores         = True
                              }
         }
 where addTimeOut _ _ = error "MathSAT: Timeout values are not supported"

       -- If unsat cores are needed, MathSAT requires an explicit command-line argument
       modConfig :: SMTConfig -> SMTConfig
       modConfig cfg
        | not (getUnsatCore cfg) = cfg
        | True                   = cfg {solver = (solver cfg) {options = newOpts}}
        where newOpts = options (solver cfg) ++ ["-unsat_core_generation=3"]
