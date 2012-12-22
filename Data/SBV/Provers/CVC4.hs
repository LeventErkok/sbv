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

{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Provers.CVC4(cvc4) where

import qualified Control.Exception as C

import Data.Char          (isDigit)
import Data.Function      (on)
import Data.List          (sortBy, intercalate)
import System.Environment (getEnv)
import System.Exit        (ExitCode(..))

import Data.SBV.BitVectors.Data
import Data.SBV.Provers.SExpr
import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib

-- | The description of the CVC4 SMT solver
-- The default executable is @\"cvc4\"@, which must be in your path. You can use the @SBV_CVC4@ environment variable to point to the executable on your system.
-- The default options are @\"--lang smt\"@. You can use the @SBV_CVC4_OPTIONS@ environment variable to override the options.
cvc4 :: SMTSolver
cvc4 = SMTSolver {
           name           = "cvc4"
         , executable     = "cvc4"
         , options        = ["--lang", "smt"]
         , engine         = \cfg isSat qinps modelMap skolemMap pgm -> do
                                    execName <-               getEnv "SBV_CVC4"          `C.catch` (\(_ :: C.SomeException) -> return (executable (solver cfg)))
                                    execOpts <- (words `fmap` getEnv "SBV_CVC4_OPTIONS") `C.catch` (\(_ :: C.SomeException) -> return (options (solver cfg)))
                                    let cfg' = cfg { solver = (solver cfg) {executable = execName, options = addTimeOut (timeOut cfg) execOpts} }
                                        tweaks = case solverTweaks cfg' of
                                                   [] -> ""
                                                   ts -> unlines $ "; --- user given solver tweaks ---" : ts ++ ["; --- end of user given tweaks ---"]
                                        script = SMTScript {scriptBody = tweaks ++ pgm, scriptModel = Just (cont skolemMap)}
                                    standardSolver cfg' script id (ProofError cfg') (interpretSolverOutput cfg' (extractMap isSat qinps modelMap . match skolemMap))
         , xformExitCode  = cvc4ExitCode
         , defaultLogic   = Just "ALL_SUPPORTED"  -- CVC4 is not happy if we don't set the logic, so fall-back to this if necessary
         }
 where zero :: Kind -> String
       zero (KBounded False 1)  = "#b0"
       zero (KBounded _     sz) = "#x" ++ replicate (sz `div` 4) '0'
       zero KUnbounded          = "0"
       zero KReal               = "0.0"
       zero (KUninterpreted s)  = error $ "SBV.CVC4.zero: Unexpected uninterpreted sort: " ++ s
       cont skolemMap = intercalate "\n" $ concatMap extract skolemMap
        where extract (Left s)        = ["(echo \"((" ++ show s ++ " " ++ zero (kindOf s) ++ "))\")"]
              extract (Right (s, [])) = ["(get-value (" ++ show s ++ "))"]
              extract (Right (s, ss)) = ["(eval (" ++ show s ++ concat [' ' : zero (kindOf a) | a <- ss] ++ "))"]
       match skolemMap = zipWith annotate (concatMap dupRight skolemMap)
         where dupRight (Left s)  = [Left s]
               dupRight (Right x) = [Right x, Right x]
               annotate (Left _)        l = l
               annotate (Right (_, [])) l = l
               annotate (Right (s, _))  l = "((" ++ show s ++ " " ++ l ++ "))"
       addTimeOut Nothing  o   = o
       addTimeOut (Just i) o
         | i < 0               = error $ "CVC4: Timeout value must be non-negative, received: " ++ show i
         | True                = o ++ ["--tlimit=" ++ show i ++ "000"]  -- SBV takes seconds, CVC4 wants milli-seconds

-- | CVC4 uses different exit codes to indicate its status, rather than the
-- standard 0 being success and non-0 being failure. Make it palatable to SBV.
-- See <http://cvc4.cs.nyu.edu/wiki/User_Manual#Exit_status> for details.
cvc4ExitCode :: ExitCode -> ExitCode
cvc4ExitCode (ExitFailure n) | n `elem` [10, 20, 0] = ExitSuccess
cvc4ExitCode ec                                     = ec

extractMap :: Bool -> [(Quantifier, NamedSymVar)] -> [(String, UnintKind)] -> [String] -> SMTModel
extractMap isSat qinps _modelMap solverLines =
   SMTModel { modelAssocs    = map snd $ sortByNodeId $ concatMap (getCounterExample inps) solverLines
            , modelUninterps = []
            , modelArrays    = []
            }
  where sortByNodeId :: [(Int, a)] -> [(Int, a)]
        sortByNodeId = sortBy (compare `on` fst)
        inps -- for "sat", display the prefix existentials. For completeness, we will drop
             -- only the trailing foralls. Exception: Don't drop anything if it's all a sequence of foralls
             | isSat = if all (== ALL) (map fst qinps)
                       then map snd qinps
                       else map snd $ reverse $ dropWhile ((== ALL) . fst) $ reverse qinps
             -- for "proof", just display the prefix universals
             | True  = map snd $ takeWhile ((== ALL) . fst) qinps

getCounterExample :: [NamedSymVar] -> String -> [(Int, (String, CW))]
getCounterExample inps line = either err extract (parseSExpr line)
  where err r =  error $  "*** Failed to parse SMT-Lib2 model output from: "
                       ++ "*** " ++ show line ++ "\n"
                       ++ "*** Reason: " ++ r ++ "\n"
        isInput ('s':v)
          | all isDigit v = let inpId :: Int
                                inpId = read v
                            in case [(s, nm) | (s@(SW _ (NodeId n)), nm) <-  inps, n == inpId] of
                                 []        -> Nothing
                                 [(s, nm)] -> Just (inpId, s, nm)
                                 matches -> error $  "SBV.SMTLib2: Cannot uniquely identify value for "
                                                  ++ 's':v ++ " in "  ++ show matches
        isInput _       = Nothing
        extract (SApp [SApp [SCon v, SNum i]])  | Just (n, s, nm) <- isInput v = [(n, (nm, mkConstCW (kindOf s) i))]
        extract (SApp [SApp [SCon v, SReal i]]) | Just (n, _, nm) <- isInput v = [(n, (nm, CW KReal      (CWAlgReal i)))]
        extract (SApp [SApp [SCon v, SCon i]])  | Just (n, s, nm) <- isInput v = [(n, (nm, CW (kindOf s) (CWUninterpreted i)))]
        extract (SApp [SApp (SCon v : r)])      | Just{}          <- isInput v = error $ "SBV.SMTLib2: Cannot extract value for " ++ show v ++ ", received:\n\t" ++  show r
        extract _                                                              = []
