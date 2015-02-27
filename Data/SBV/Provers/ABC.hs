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

import qualified Control.Exception as C

import Data.Function      (on)
import Data.List          (intercalate, sortBy)
import System.Environment (getEnv)

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.PrettyNum (mkSkolemZero)
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
         , options        = ["-S", "%blast; &put; dsat -s"]
         , engine         = \cfg isSat qinps modelMap skolemMap pgm -> do
                                    execName <-               getEnv "SBV_ABC"          `C.catch` (\(_ :: C.SomeException) -> return (executable (solver cfg)))
                                    execOpts <- (words `fmap` getEnv "SBV_ABC_OPTIONS") `C.catch` (\(_ :: C.SomeException) -> return (options (solver cfg)))
                                    let cfg' = cfg { solver = (solver cfg) {executable = execName, options = execOpts} }
                                        tweaks = case solverTweaks cfg' of
                                                   [] -> ""
                                                   ts -> unlines $ "; --- user given solver tweaks ---" : ts ++ ["; --- end of user given tweaks ---"]
                                        script = SMTScript {scriptBody = tweaks ++ pgm, scriptModel = Just (cont (roundingMode cfg) skolemMap)}
                                    standardSolver cfg' script id (ProofError cfg') (interpretSolverOutput cfg' (extractMap isSat qinps modelMap))
         , xformExitCode  = id
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
 where cont rm skolemMap = intercalate "\n" $ map extract skolemMap
        where extract (Left s)        = "(echo \"((" ++ show s ++ " " ++ mkSkolemZero rm (kindOf s) ++ "))\")"
              extract (Right (s, [])) = "(get-value (" ++ show s ++ "))"
              extract (Right (s, ss)) = "(get-value (" ++ show s ++ concat [' ' : mkSkolemZero rm (kindOf a) | a <- ss] ++ "))"

extractMap :: Bool -> [(Quantifier, NamedSymVar)] -> [(String, UnintKind)] -> [String] -> SMTModel
extractMap isSat qinps _modelMap solverLines =
   SMTModel { modelAssocs    = map snd $ sortByNodeId $ concatMap (interpretSolverModelLine inps) solverLines
            , modelUninterps = []
            , modelArrays    = []
            }
  where sortByNodeId :: [(Int, a)] -> [(Int, a)]
        sortByNodeId = sortBy (compare `on` fst)
        inps -- for "sat", display the prefix existentials. For completeness, we will drop
             -- only the trailing foralls. Exception: Don't drop anything if it's all a sequence of foralls
             | isSat = map snd $ if all (== ALL) (map fst qinps)
                                 then qinps
                                 else reverse $ dropWhile ((== ALL) . fst) $ reverse qinps
             -- for "proof", just display the prefix universals
             | True  = map snd $ takeWhile ((== ALL) . fst) qinps
