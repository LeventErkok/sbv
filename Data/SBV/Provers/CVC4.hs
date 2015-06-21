-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.CVC4
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- The connection to the CVC4 SMT solver
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Provers.CVC4(cvc4) where

import Data.SBV.BitVectors.Data
import Data.SBV.SMT.SMT

-- | The description of the CVC4 SMT solver
-- The default executable is @\"cvc4\"@, which must be in your path. You can use the @SBV_CVC4@ environment variable to point to the executable on your system.
-- The default options are @\"--lang smt\"@. You can use the @SBV_CVC4_OPTIONS@ environment variable to override the options.
cvc4 :: SMTSolver
cvc4 = SMTSolver {
           name         = CVC4
         , executable   = "cvc4"
         , options      = ["--lang", "smt"]
         , engine       = standardEngine "SBV_CVC4" "SBV_CVC4_OPTIONS" addTimeOut standardModel
         , capabilities = SolverCapabilities {
                                capSolverName              = "CVC4"
                              , mbDefaultLogic             = Just "ALL_SUPPORTED"  -- CVC4 is not happy if we don't set the logic, so fall-back to this if necessary
                              , supportsMacros             = True
                              , supportsProduceModels      = True
                              , supportsQuantifiers        = True
                              , supportsUninterpretedSorts = True
                              , supportsUnboundedInts      = True
                              , supportsReals              = True  -- Not quite the same capability as Z3; but works more or less..
                              , supportsFloats             = False
                              , supportsDoubles            = False
                              }
         }
 where addTimeOut o i | i < 0 = error $ "CVC4: Timeout value must be non-negative, received: " ++ show i
                      | True  = o ++ ["--tlimit=" ++ show i ++ "000"]  -- SBV takes seconds, CVC4 wants milli-seconds
