-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.Yices
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- The connection to the Yices SMT solver
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Provers.Yices(yices) where

import Data.SBV.Core.Data
import Data.SBV.SMT.SMT

-- | The description of the Yices SMT solver
-- The default executable is @\"yices-smt2\"@, which must be in your path. You can use the @SBV_YICES@ environment variable to point to the executable on your system.
-- SBV does not pass any arguments to yices. You can use the @SBV_YICES_OPTIONS@ environment variable to override the options.
yices :: SMTSolver
yices = SMTSolver {
           name         = Yices
         , executable   = "yices-smt2"
         , options      = const ["--incremental"]
         , engine       = standardEngine "SBV_YICES" "SBV_YICES_OPTIONS"
         , capabilities = SolverCapabilities {
                                supportsQuantifiers        = False
                              , supportsUninterpretedSorts = True
                              , supportsUnboundedInts      = True
                              , supportsReals              = True
                              , supportsApproxReals        = False
                              , supportsIEEE754            = False
                              , supportsOptimization       = False
                              , supportsPseudoBooleans     = False
                              , supportsCustomQueries      = True
                              , supportsGlobalDecls        = False
                              , supportsFlattenedSequences = Nothing
                              }
         }
