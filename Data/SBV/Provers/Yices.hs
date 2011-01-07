{- (c) Copyright Levent Erkok. All rights reserved.
--
-- The sbv library is distributed with the BSD3 license. See the LICENSE file
-- in the distribution for details.
-}

{-# LANGUAGE PatternGuards #-}

module Data.SBV.Provers.Yices(yices, timeout) where

import Data.Char(isDigit)
import Data.List(sortBy, isPrefixOf)
import Data.SBV.BitVectors.Data
import Data.SBV.SMT.SMT
import Data.SBV.Provers.SExpr

yices :: SMTSolver
yices = SMTSolver {
           name       = "Yices"
         , executable = "yices"
         -- , options    = ["-tc", "-smt", "-e"]   -- For Yices1
         , options    = ["-m", "-f"]  -- For Yices2
         , engine     = \cfg inps pgm -> standardSolver cfg pgm (ProofError cfg) (interpret cfg inps)
         }

timeout :: Int -> SMTSolver -> SMTSolver
timeout n s
  | n <= 0 = error $ "Yices.timeout value should be > 0, received: " ++ show n
  | True   = s{options = options s ++ ["-t", show n]}

sortByNodeId :: [(Int, a)] -> [(Int, a)]
sortByNodeId = sortBy (\(x, _) (y, _) -> compare x y)

interpret :: SMTConfig -> [NamedSymVar] -> [String] -> SMTResult
interpret cfg _    ("unsat":_)      = Unsatisfiable cfg
interpret cfg inps ("unknown":rest) = Unknown       cfg  $ map (\(_, y) -> y) $ sortByNodeId $ concatMap (getCounterExample inps) rest
interpret cfg inps ("sat":rest)     = Satisfiable   cfg  $ map (\(_, y) -> y) $ sortByNodeId $ concatMap (getCounterExample inps) rest
interpret cfg _    ("timeout":_)    = TimeOut       cfg
interpret cfg _    ls               = ProofError    cfg  $ ls

getCounterExample :: [NamedSymVar] -> String -> [(Int, (String, CW))]
getCounterExample inps line
    | isComment line = []
    | True           = either err extract (parseSExpr line)
  where err r =  error $  "*** Failed to parse Yices model output from: "
                       ++ "*** " ++ show line ++ "\n"
                       ++ "*** Reason: " ++ r ++ "\n"
        isInput ('s':v)
          | all isDigit v = let inpId :: Int
                                inpId = read v
                            in case [(s, nm) | (s@(SW _ (NodeId n)), nm) <-  inps, n == inpId] of
                                 []        -> Nothing
                                 [(s, nm)] -> Just (inpId, s, nm)
                                 matches -> error $  "SBV.Yices: Cannot uniquely identify value for "
                                                  ++ 's':v ++ " in "  ++ show matches
        isInput _       = Nothing
        extract (S_App [S_Con "=", S_Con v, S_Num i]) | Just (n, s, nm) <- isInput v = [(n, (nm, mkConstCW (hasSign s, sizeOf s) i))]
        extract (S_App [S_Con "=", S_Num i, S_Con v]) | Just (n, s, nm) <- isInput v = [(n, (nm, mkConstCW (hasSign s, sizeOf s) i))]
        extract _                                                                    = []

-- this is largely by observation of Yices output; not quite sure if it captures all
isComment :: String -> Bool
isComment s = any (`isPrefixOf` s) prefixes
  where prefixes = ["---", "default"]
