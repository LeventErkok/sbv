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

{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Provers.Yices(yices) where

import qualified Control.Exception as C

import Data.Function      (on)
import Data.List          (sortBy, intercalate)
import System.Environment (getEnv)

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.PrettyNum (mkSkolemZero)
import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib
import Data.SBV.Utils.Lib (splitArgs)

-- | The description of the Yices SMT solver
-- The default executable is @\"yices-smt2\"@, which must be in your path. You can use the @SBV_YICES@ environment variable to point to the executable on your system.
-- SBV does not pass any arguments to yices. You can use the @SBV_YICES_OPTIONS@ environment variable to override the options.
yices :: SMTSolver
yices = SMTSolver {
           name           = Yices
         , executable     = "yices-smt2"
         , options        = []
         , engine         = \cfg isSat qinps modelMap skolemMap pgm -> do
                                    execName <-                    getEnv "SBV_YICES"          `C.catch` (\(_ :: C.SomeException) -> return (executable (solver cfg)))
                                    execOpts <- (splitArgs `fmap`  getEnv "SBV_YICES_OPTIONS") `C.catch` (\(_ :: C.SomeException) -> return (options (solver cfg)))
                                    let cfg'   = cfg {solver = (solver cfg) {executable = execName, options = addTimeOut (timeOut cfg) execOpts}}
                                        tweaks = case solverTweaks cfg' of
                                                   [] -> ""
                                                   ts -> unlines $ "; --- user given solver tweaks ---" : ts ++ ["; --- end of user given tweaks ---"]
                                        script = SMTScript {scriptBody = tweaks ++ pgm, scriptModel = Just (cont (roundingMode cfg) skolemMap)}
                                    standardSolver cfg' script id (ProofError cfg') (interpretSolverOutput cfg' (extractMap isSat qinps modelMap))
         , xformExitCode  = id
         , capabilities   = SolverCapabilities {
                                  capSolverName              = "Yices"
                                , mbDefaultLogic             = Nothing
                                , supportsMacros             = True
                                , supportsProduceModels      = True
                                , supportsQuantifiers        = False
                                , supportsUninterpretedSorts = True
                                , supportsUnboundedInts      = True
                                , supportsReals              = True
                                , supportsFloats             = False
                                , supportsDoubles            = False
                                }
         }
  where cont rm skolemMap = intercalate "\n" $ map extract skolemMap
         where extract (Left s)        = "(echo \"((" ++ show s ++ " " ++ mkSkolemZero rm (kindOf s) ++ "))\")"
               extract (Right (s, [])) = "(get-value (" ++ show s ++ "))"
               extract (Right (s, ss)) = "(get-value (" ++ show s ++ concat [' ' : mkSkolemZero rm (kindOf a) | a <- ss] ++ "))"
        addTimeOut Nothing  o   = o
        addTimeOut (Just _) _   = error "Yices: Timeout values are not supported by Yices"

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
