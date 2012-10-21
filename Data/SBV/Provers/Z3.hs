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

{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Provers.Z3(z3) where

import qualified Control.Exception as C

import Data.Char          (isDigit, toLower)
import Data.Function      (on)
import Data.List          (sortBy, intercalate, isPrefixOf, groupBy)
import System.Environment (getEnv)
import qualified System.Info as S(os)

import Data.SBV.BitVectors.AlgReals
import Data.SBV.BitVectors.Data
import Data.SBV.Provers.SExpr
import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib

-- Choose the correct prefix character for passing options
-- TBD: Is there a more foolproof way of determining this?
optionPrefix :: Char
optionPrefix
  | map toLower S.os `elem` ["linux", "darwin"] = '-'
  | True                                        = '/'   -- windows

-- | The description of the Z3 SMT solver
-- The default executable is @\"z3\"@, which must be in your path. You can use the @SBV_Z3@ environment variable to point to the executable on your system.
-- The default options are @\"\/in \/smt2\"@, which is valid for Z3 3.2. You can use the @SBV_Z3_OPTIONS@ environment variable to override the options.
z3 :: SMTSolver
z3 = SMTSolver {
           name       = "z3"
         , executable = "z3"
         , options    = map (optionPrefix:) ["in", "smt2"]
         , engine     = \cfg isSat qinps modelMap skolemMap pgm -> do
                                execName <-               getEnv "SBV_Z3"          `C.catch` (\(_ :: C.SomeException) -> return (executable (solver cfg)))
                                execOpts <- (words `fmap` getEnv "SBV_Z3_OPTIONS") `C.catch` (\(_ :: C.SomeException) -> return (options (solver cfg)))
                                let cfg' = cfg { solver = (solver cfg) {executable = execName, options = addTimeOut (timeOut cfg) execOpts} }
                                    tweaks = case solverTweaks cfg' of
                                               [] -> ""
                                               ts -> unlines $ "; --- user given solver tweaks ---" : ts ++ ["; --- end of user given tweaks ---"]
                                    dlim = printRealPrec cfg'
                                    ppDecLim = "(set-option :pp-decimal-precision " ++ show dlim ++ ")\n"
                                    script = SMTScript {scriptBody = tweaks ++ ppDecLim ++ pgm, scriptModel = Just (cont skolemMap)}
                                if dlim < 1
                                   then error $ "SBV.Z3: printRealPrec value should be at least 1, invalid value received: " ++ show dlim
                                   else standardSolver cfg' script cleanErrs (ProofError cfg') (interpretSolverOutput cfg' (extractMap isSat qinps modelMap . match skolemMap))
         }
 where -- Get rid of the following when z3_4.0 is out
       cleanErrs = intercalate "\n" . filter (not . junk) . lines
       junk = ("WARNING:" `isPrefixOf`)
       zero :: Kind -> String
       zero (KBounded False 1)  = "#b0"
       zero (KBounded _     sz) = "#x" ++ replicate (sz `div` 4) '0'
       zero KUnbounded          = "0"
       zero KReal               = "0.0"
       zero (KUninterpreted s)  = error $ "SBV.Z3.zero: Unexpected uninterpreted sort: " ++ s
       cont skolemMap = intercalate "\n" $ concatMap extract skolemMap
        where extract (Left s)        = ["(echo \"((" ++ show s ++ " " ++ zero (kindOf s) ++ "))\")"]
              extract (Right (s, [])) = let g = "(get-value (" ++ show s ++ "))" in getVal (kindOf s) g
              extract (Right (s, ss)) = let g = "(eval (" ++ show s ++ concat [' ' : zero (kindOf a) | a <- ss] ++ "))" in getVal (kindOf s) g
              getVal KReal g = ["(set-option :pp-decimal false)", g, "(set-option :pp-decimal true)", g]
              getVal _     g = [g]
       match skolemMap = zipWith annotate (concatMap dupRight skolemMap)
         where dupRight (Left s)  = [Left s]
               dupRight (Right x) = [Right x, Right x]
               annotate (Left _)        l = l
               annotate (Right (_, [])) l = l
               annotate (Right (s, _))  l = "((" ++ show s ++ " " ++ l ++ "))"
       addTimeOut Nothing  o   = o
       addTimeOut (Just i) o
         | i < 0               = error $ "Z3: Timeout value must be non-negative, received: " ++ show i
         | True                = o ++ [optionPrefix : "T:" ++ show i]

extractMap :: Bool -> [(Quantifier, NamedSymVar)] -> [(String, UnintKind)] -> [String] -> SMTModel
extractMap isSat qinps _modelMap solverLines =
   SMTModel { modelAssocs    = map snd $ squashReals $ sortByNodeId $ concatMap (getCounterExample inps) solverLines
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
        squashReals :: [(Int, (String, CW))] -> [(Int, (String, CW))]
        squashReals = concatMap squash . groupBy ((==) `on` fst)
          where squash [(i, (n, cw1)), (_, (_, cw2))] = [(i, (n, mergeReals n cw1 cw2))]
                squash xs = xs
                mergeReals :: String -> CW -> CW -> CW
                mergeReals n (CW KReal (CWAlgReal a)) (CW KReal (CWAlgReal b)) = CW KReal (CWAlgReal (mergeAlgReals (error (bad n a b)) a b))
                mergeReals n a b = error $ bad n a b
                bad n a b = "SBV.Z3: Cannot merge reals for variable: " ++ n ++ " received: " ++ show (a, b)

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
