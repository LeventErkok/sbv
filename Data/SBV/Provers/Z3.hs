-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.Z3
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- The connection to the Z3 SMT solver
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Provers.Z3(z3) where

import qualified Control.Exception as C

import Data.Char          (toLower)
import Data.Function      (on)
import Data.List          (sortBy, groupBy)
import System.Environment (getEnv)
import qualified System.Info as S(os)

import Data.SBV.Core.AlgReals
import Data.SBV.Core.Data
import Data.SBV.Control.Types (SMTOption(OptionKeyword), setSMTOption)

import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib

import Data.SBV.Utils.Lib (splitArgs)
import Data.SBV.Utils.PrettyNum

-- Choose the correct prefix character for passing options
-- TBD: Is there a more foolproof way of determining this?
optionPrefix :: Char
optionPrefix
  | map toLower S.os `elem` ["linux", "darwin"] = '-'
  | True                                        = '/'   -- windows

-- | The description of the Z3 SMT solver
-- The default executable is @\"z3\"@, which must be in your path. You can use the @SBV_Z3@ environment variable to point to the executable on your system.
-- The default options are @\"-in -smt2\"@, which is valid for Z3 4.1. You can use the @SBV_Z3_OPTIONS@ environment variable to override the options.
z3 :: SMTSolver
z3 = SMTSolver {
           name           = Z3
         , executable     = "z3"
         , options        = map (optionPrefix:) ["nw", "in", "smt2"]

         , engine         = \cfg ctx isSat mbOptInfo qinps skolemMap pgm -> do

                                    execName <-                   getEnv "SBV_Z3"          `C.catch` (\(_ :: C.SomeException) -> return (executable (solver cfg)))
                                    execOpts <- (splitArgs `fmap` getEnv "SBV_Z3_OPTIONS") `C.catch` (\(_ :: C.SomeException) -> return (options (solver cfg)))

                                    let cfg'   = cfg {solver = (solver cfg) {executable = execName, options = execOpts}}

                                        mkCont   = cont (roundingMode cfg') skolemMap

                                        (nModels, mbContScript) =
                                                case mbOptInfo of
                                                  Just (Independent, n) | n > 1 -> (n, concatMap (mkCont . Just) [0 .. n-1])
                                                  _                             -> (1, mkCont Nothing)

                                        extraOptions = [OptionKeyword ":pp.decimal_precision" [show (printRealPrec cfg)]]

                                        script = SMTScript { scriptBody  = unlines (map setSMTOption extraOptions) ++ pgm
                                                           , scriptModel = mbContScript
                                                           }

                                        mkResult c em
                                         | nModels == 1 = replicate 1 . interpretSolverOutput              c em
                                         | True         =               interpretSolverOutputMulti nModels c em

                                    standardSolver cfg' ctx script id (replicate nModels . ProofError cfg') (mkResult cfg' (extractMap isSat qinps))

         , capabilities   = SolverCapabilities {
                                  supportsQuantifiers        = True
                                , supportsUninterpretedSorts = True
                                , supportsUnboundedInts      = True
                                , supportsReals              = True
                                , supportsIEEE754            = True
                                , supportsOptimization       = True
                                , supportsPseudoBooleans     = True
                                , supportsCustomQueries      = True
                                }
         }
 where cont rm skolemMap mbModelIndex = wrapModel grabValues
        where grabValues = concatMap extract skolemMap

              modelIndex = case mbModelIndex of
                             Nothing -> ""
                             Just i  -> " :model_index " ++ show i

              wrapModel xs = case mbModelIndex of
                               Just _ -> let marker = "(echo " ++ show multiModelSeparator ++ ")" in marker : xs
                               _      -> xs

              -- In the skolemMap:
              --    * Left's are universals: i.e., the model should be true for any of these. So, we do not query for these.
              --    * Right's are existentials. If there are no dependencies (empty list), then we can
              --      simply use get-value to extract it's value. Otherwise, we have to apply it to
              --      an appropriate number of 0's to get the final value.
              extract (Left _)        = []
              extract (Right (s, [])) = let g = "(get-value (" ++ show s ++ ")" ++ modelIndex ++ ")" in getVal (kindOf s) g
              extract (Right (s, ss)) = let g = "(get-value ((" ++ show s ++ concat [' ' : mkSkolemZero rm (kindOf a) | a <- ss] ++ "))" ++ modelIndex ++ ")" in getVal (kindOf s) g

              getVal KReal g = ["(set-option :pp.decimal false) " ++ g, "(set-option :pp.decimal true)  " ++ g]
              getVal _     g = [g]

extractMap :: Bool -> [(Quantifier, NamedSymVar)] -> [String] -> SMTModel
extractMap isSat qinps solverLines =
   SMTModel { modelObjectives = map snd $               sortByNodeId $ concatMap (interpretSolverObjectiveLine inps) solverLines
            , modelAssocs     = map snd $ squashReals $ sortByNodeId $ concatMap (interpretSolverModelLine     inps) solverLines
            }
  where sortByNodeId :: [(Int, a)] -> [(Int, a)]
        sortByNodeId = sortBy (compare `on` fst)

        -- for "sat",   display the existentials.
        -- for "proof", display the universals.
        inps | isSat = map snd $ takeWhile ((/= ALL) . fst) qinps
             | True  = map snd $ takeWhile ((== ALL) . fst) qinps

        squashReals :: [(Int, (String, CW))] -> [(Int, (String, CW))]
        squashReals = concatMap squash . groupBy ((==) `on` fst)
          where squash [(i, (n, cw1)), (_, (_, cw2))] = [(i, (n, mergeReals n cw1 cw2))]
                squash xs = xs

                mergeReals :: String -> CW -> CW -> CW
                mergeReals n (CW KReal (CWAlgReal a)) (CW KReal (CWAlgReal b)) = CW KReal (CWAlgReal (mergeAlgReals (bad n a b) a b))
                mergeReals n a b = bad n a b

                bad n a b = error $ "SBV.Z3: Cannot merge reals for variable: " ++ n ++ " received: " ++ show (a, b)
