-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.Boolector
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- The connection to the Boolector SMT solver
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Provers.Boolector(boolector) where

import qualified Control.Exception as C

import Data.Function      (on)
import Data.List          (sortBy, intercalate)
import System.Environment (getEnv)
import System.Exit        (ExitCode(..))

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.PrettyNum (mkSkolemZero)
import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib
import Data.SBV.Utils.Lib (splitArgs)

-- | The description of the Boolector SMT solver
-- The default executable is @\"boolector\"@, which must be in your path. You can use the @SBV_BOOLECTOR@ environment variable to point to the executable on your system.
-- The default options are @\"-m --smt2\"@. You can use the @SBV_BOOLECTOR_OPTIONS@ environment variable to override the options.
boolector :: SMTSolver
boolector = SMTSolver {
           name           = Boolector
         , executable     = "boolector"
         , options        = ["--smt2", "--smt2-model"]
         , engine         = \cfg _isSat qinps modelMap skolemMap pgm -> do
                                    execName <-                   getEnv "SBV_BOOLECTOR"          `C.catch` (\(_ :: C.SomeException) -> return (executable (solver cfg)))
                                    execOpts <- (splitArgs `fmap` getEnv "SBV_BOOLECTOR_OPTIONS") `C.catch` (\(_ :: C.SomeException) -> return (options (solver cfg)))
                                    let cfg' = cfg {solver = (solver cfg) {executable = execName, options = addTimeOut (timeOut cfg) execOpts}}
                                        tweaks = case solverTweaks cfg' of
                                                   [] -> ""
                                                   ts -> unlines $ "; --- user given solver tweaks ---" : ts ++ ["; --- end of user given tweaks ---"]
                                        script = SMTScript {scriptBody = tweaks ++ pgm, scriptModel = Just (cont (roundingMode cfg) skolemMap)}
                                    standardSolver cfg' script id (ProofError cfg') (interpretSolverOutput cfg' (extractMap (map snd qinps) modelMap))
         , xformExitCode  = boolectorExitCode
         , capabilities   = SolverCapabilities {
                                  capSolverName              = "Boolector"
                                , mbDefaultLogic             = Nothing
                                , supportsMacros             = False
                                , supportsProduceModels      = True
                                , supportsQuantifiers        = False
                                , supportsUninterpretedSorts = False
                                , supportsUnboundedInts      = False
                                , supportsReals              = False
                                , supportsFloats             = False
                                , supportsDoubles            = False
                                }
         }
 where addTimeOut Nothing  o   = o
       addTimeOut (Just i) o
         | i < 0               = error $ "Boolector: Timeout value must be non-negative, received: " ++ show i
         | True                = o ++ ["-t=" ++ show i]
       cont rm skolemMap = intercalate "\n" $ map extract skolemMap
        where extract (Left s)        = "(echo \"((" ++ show s ++ " " ++ mkSkolemZero rm (kindOf s) ++ "))\")"
              extract (Right (s, [])) = "(get-value (" ++ show s ++ "))"
              extract (Right (s, ss)) = "(get-value (" ++ show s ++ concat [' ' : mkSkolemZero rm (kindOf a) | a <- ss] ++ "))"

-- | Similar to CVC4, Boolector uses different exit codes to indicate its status.
boolectorExitCode :: ExitCode -> ExitCode
boolectorExitCode (ExitFailure n) | n `elem` [10, 20, 0] = ExitSuccess
boolectorExitCode ec                                     = ec

extractMap :: [NamedSymVar] -> [(String, UnintKind)] -> [String] -> SMTModel
extractMap inps _modelMap solverLines =
   SMTModel { modelAssocs    = map snd $ sortByNodeId $ concatMap (interpretSolverModelLine inps) solverLines
            , modelUninterps = []
            , modelArrays    = []
            }
  where sortByNodeId :: [(Int, a)] -> [(Int, a)]
        sortByNodeId = sortBy (compare `on` fst)
