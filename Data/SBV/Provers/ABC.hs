-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.ABC
-- Copyright   :  (c) Adam Foltzer
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- The connection to the ABC verification and synthesis tool
-----------------------------------------------------------------------------

module Data.SBV.Provers.ABC(abc) where

import Data.SBV.Core.Data
import Data.SBV.SMT.SMT

-- | The description of abc. The default executable is @\"abc\"@,
-- which must be in your path. You can use the @SBV_ABC@ environment
-- variable to point to the executable on your system.  The default
-- options are @-S \"%blast; &sweep -C 5000; &syn4; &cec -s -m -C 2000\"@.
-- You can use the @SBV_ABC_OPTIONS@ environment variable to override the options.
abc :: SMTSolver
abc = SMTSolver {
           name         = ABC
         , executable   = "abc"
         , options      = ["-S", "%blast; &sweep -C 5000; &syn4; &cec -s -m -C 2000"]
         , engine       = standardEngine "SBV_ABC" "SBV_ABC_OPTIONS" addTimeOut standardModel
         , capabilities = SolverCapabilities {
                                capSolverName              = "ABC"
                              , mbDefaultLogic             = const Nothing
                              , supportsMacros             = True
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
  where addTimeOut _ _ = error "ABC: Timeout values are not supported"
