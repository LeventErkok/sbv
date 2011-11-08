-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.Z3
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- The connection to the Z3 SMT solver
-----------------------------------------------------------------------------

{-# LANGUAGE PatternGuards #-}

module Data.SBV.Provers.Z3(z3) where

import Data.Char          (isDigit)
import Data.List          (sortBy, intercalate, isPrefixOf)
import System.Environment (getEnv)
import qualified System.Info as S(os)

import Data.SBV.BitVectors.Data
import Data.SBV.Provers.SExpr
import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib

-- | The description of the Z3 SMT solver
-- The default executable is @\"z3\"@, which must be in your path. You can use the @SBV_Z3@ environment variable to point to the executable on your system.
-- The default options are @\"\/in \/smt2\"@, which is valid for Z3 3.2. You can use the @SBV_Z3_OPTIONS@ environment variable to override the options.
z3 :: SMTSolver
z3 = SMTSolver {
           name       = "z3"
         , executable = "z3"
         , options    = if S.os == "linux" then ["-in", "-smt2"] else ["/in", "/smt2"]
         , engine     = \cfg isSat qinps modelMap skolemMap pgm -> do
                                execName <-               getEnv "SBV_Z3"          `catch` (\_ -> return (executable (solver cfg)))
                                execOpts <- (words `fmap` getEnv "SBV_Z3_OPTIONS") `catch` (\_ -> return (options (solver cfg)))
                                let cfg' = cfg { solver = (solver cfg) {executable = execName, options = addTimeOut (timeOut cfg) execOpts} }
                                    script = SMTScript { scriptBody = "(set-option :mbqi true)\n" ++ pgm, scriptModel = Just (cont skolemMap)}
                                standardSolver cfg' script cleanErrs (ProofError cfg) (interpretSolverOutput cfg (extractMap isSat qinps modelMap . zipWith match skolemMap))
         }
 where -- This is quite crude and failure prone.. But is necessary to get z3 working through Wine on Mac
       cleanErrs = intercalate "\n" . filter (not . junk) . lines
       junk "fixme:heap:HeapSetInformation 0x0 1 0x0 0" = True
       junk s | "WARNING:" `isPrefixOf` s               = True
       junk _                                           = False
       zero :: Int -> String
       zero 1  = "#b0"
       zero sz = "#x" ++ replicate (sz `div` 4) '0'
       cont skolemMap = intercalate "\n" $ map extract skolemMap
        where extract (Left s)        = "(echo \"((" ++ show s ++ " " ++ zero (sizeOf s) ++ "))\")"
              extract (Right (s, [])) = "(get-value (" ++ show s ++ "))"
              extract (Right (s, ss)) = "(eval (" ++ show s ++ concat [' ' : zero (sizeOf a) | a <- ss] ++ "))"
       match (Left _)        l = l
       match (Right (_, [])) l = l
       match (Right (s, _))  l = "((" ++ show s ++ " " ++ l ++ "))"
       addTimeOut Nothing  o   = o
       addTimeOut (Just i) o
         | i < 0               = error $ "Z3: Timeout value must be non-negative, received: " ++ show i
         | S.os == "linux"     = o ++ ["-T:" ++ show i]
         | True                = o ++ ["/T:" ++ show i]

extractMap :: Bool -> [(Quantifier, NamedSymVar)] -> [(String, UnintKind)] -> [String] -> SMTModel
extractMap isSat qinps _modelMap solverLines =
   SMTModel { modelAssocs    = map snd $ sortByNodeId $ concatMap (getCounterExample inps) solverLines
            , modelUninterps = []
            , modelArrays    = []
            }
  where sortByNodeId :: [(Int, a)] -> [(Int, a)]
        sortByNodeId = sortBy (\(x, _) (y, _) -> compare x y)
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
        extract (S_App [S_App [S_Con v, S_Num i]]) | Just (n, s, nm) <- isInput v = [(n, (nm, mkConstCW (hasSign s, sizeOf s) i))]
        extract _                                                                 = []
