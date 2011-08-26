-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.Z3_QBVF
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- The connection to the QBVF solver as provided by Z3
-----------------------------------------------------------------------------

{-# LANGUAGE PatternGuards #-}

module Data.SBV.Provers.Z3_QBVF(z3) where

import Data.Char          (isDigit)
import Data.List          (sortBy, intercalate)
import System.Environment (getEnv)

import Data.SBV.BitVectors.Data
import Data.SBV.Provers.SExpr
import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib

-- | The description of the Z3 SMT solver
-- The default executable is @\"z3\"@, which must be in your path. You can use the @SBV_Z3@ environment variable to point to the executable on your system.
-- The default options are @\"\/in \/smt2\"@, which is valid for Z3 3.0 series. You can use the @SBV_Z3_OPTIONS@ environment variable to override the options.
z3 :: SMTSolver
z3 = SMTSolver {
           name       = "z3"
         , executable = "z3"
         , options    = ["/in", "/smt2"]
         , engine     = \cfg inps modelMap pgm -> do
                                execName <-                getEnv "SBV_Z3"           `catch` (\_ -> return (executable (solver cfg)))
                                execOpts <- (words `fmap` (getEnv "SBV_Z3_OPTIONS")) `catch` (\_ -> return (options (solver cfg)))
                                let cfg' = cfg { solver = (solver cfg) {executable = execName, options = execOpts} }
                                standardSolver cfg' pgm cleanErrs (ProofError cfg) (interpretSolverOutput cfg (extractMap inps modelMap))
         }
 where -- This is quite crude and failure prone.. But is necessary to get z3 working through Wine on Mac
       cleanErrs = intercalate "\n" . filter (not . junk) . lines
       junk "fixme:heap:HeapSetInformation 0x0 1 0x0 0" = True
       junk _                                           = False

extractMap :: [NamedSymVar] -> [(String, UnintKind)] -> [String] -> SMTModel
extractMap inps _modelMap solverLines =
   SMTModel { modelAssocs    = map (\(_, y) -> y) $ sortByNodeId $ concatMap (getCounterExample inps) solverLines
            , modelUninterps = []
            , modelArrays    = []
            }
  where sortByNodeId :: [(Int, a)] -> [(Int, a)]
        sortByNodeId = sortBy (\(x, _) (y, _) -> compare x y)

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
