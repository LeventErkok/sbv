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

{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Provers.ABC(abc) where

import Data.Function      (on)
import Data.List          (sortBy)

import Data.SBV.BitVectors.Data
import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib

-- | The description of abc. The default executable is @\"abc\"@,
-- which must be in your path. You can use the @SBV_ABC@ environment
-- variable to point to the executable on your system.  There are no
-- default options. You can use the @SBV_ABC_OPTIONS@ environment
-- variable to override the options.
abc :: SMTSolver
abc = SMTSolver {
           name           = ABC
         , executable     = "abc"
         , options        = ["-S", "%blast; &sweep -C 5000; &syn4; &cec -s -m -C 2000"]
         , engine         = standardEngine "SBV_ABC" "SBV_ABC_OPTIONS" addTimeOut extractMap
         , capabilities   = SolverCapabilities {
                                  capSolverName              = "ABC"
                                , mbDefaultLogic             = Nothing
                                , supportsMacros             = True
                                , supportsProduceModels      = True
                                , supportsQuantifiers        = False
                                , supportsUninterpretedSorts = False
                                , supportsUnboundedInts      = False
                                , supportsReals              = False
                                , supportsFloats             = False
                                , supportsDoubles            = False
                                }
         }
  where addTimeOut _ _ = error "Yices: Timeout values are not supported by Yices"

extractMap :: Bool -> [(Quantifier, NamedSymVar)] -> [String] -> SMTModel
extractMap isSat qinps solverLines =
   SMTModel { modelAssocs    = map snd $ sortByNodeId $ concatMap (interpretSolverModelLine inps) solverLines }
  where sortByNodeId :: [(Int, a)] -> [(Int, a)]
        sortByNodeId = sortBy (compare `on` fst)
        inps -- for "sat", display the prefix existentials. For completeness, we will drop
             -- only the trailing foralls. Exception: Don't drop anything if it's all a sequence of foralls
             | isSat = map snd $ if all (== ALL) (map fst qinps)
                                 then qinps
                                 else reverse $ dropWhile ((== ALL) . fst) $ reverse qinps
             -- for "proof", just display the prefix universals
             | True  = map snd $ takeWhile ((== ALL) . fst) qinps
