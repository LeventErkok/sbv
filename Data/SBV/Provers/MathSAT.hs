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

import Data.Function      (on)
import Data.List          (sortBy)

import Data.SBV.BitVectors.Data
import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib

-- | The description of the MathSAT SMT solver
-- The default executable is @\"mathsat\"@, which must be in your path. You can use the @SBV_MATHSAT@ environment variable to point to the executable on your system.
-- The default options are @\"-input=smt2\"@. You can use the @SBV_MATHSAT_OPTIONS@ environment variable to override the options.
mathSAT :: SMTSolver
mathSAT = SMTSolver {
           name           = MathSAT
         , executable     = "mathsat"
         , options        = ["-input=smt2"]
         , engine         = standardEngine "SBV_MATHSAT" "SBV_MATHSAT_OPTIONS" addTimeOut extractMap
         , capabilities   = SolverCapabilities {
                                  capSolverName              = "MathSAT"
                                , mbDefaultLogic             = Nothing
                                , supportsMacros             = False
                                , supportsProduceModels      = True
                                , supportsQuantifiers        = True
                                , supportsUninterpretedSorts = True
                                , supportsUnboundedInts      = True
                                , supportsReals              = True
                                , supportsFloats             = True
                                , supportsDoubles            = True
                                }
         }
 where addTimeOut _ _ = error "MathSAT: Timeout values are not supported by MathSat"

extractMap :: Bool -> [(Quantifier, NamedSymVar)] -> [String] -> SMTModel
extractMap _isSat qinps solverLines =
   SMTModel { modelAssocs = map snd $ sortByNodeId $ concatMap (interpretSolverModelLine (map snd qinps) . cvt) solverLines }
  where sortByNodeId :: [(Int, a)] -> [(Int, a)]
        sortByNodeId = sortBy (compare `on` fst)
        cvt :: String -> String
        cvt s = case words s of
                  [var, val] -> "((" ++ var ++ " #b" ++ map tr val ++ "))"
                  _          -> s -- good-luck..
          where tr 'x' = '0'
                tr x   = x
