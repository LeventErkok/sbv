-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.Yices
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- The connection to the Yices SMT solver
-----------------------------------------------------------------------------

{-# LANGUAGE PatternGuards #-}

module Data.SBV.Provers.Yices(yices, timeout) where

import Control.Monad      (foldM)
import Data.Char          (isDigit)
import Data.List          (sortBy, isPrefixOf)
import System.Environment (getEnv)

import Data.SBV.BitVectors.Data
import Data.SBV.Provers.SExpr
import Data.SBV.SMT.SMT

-- | The description of the Yices SMT solver
-- The default executable is @\"yices\"@, which must be in your path. You can use the @SBV_YICES@ environment variable to point to the executable on your system.
-- The default options are @\"-m -f\"@, which is valid for Yices 2 series. You can use the @SBV_YICES_OPTIONS@ environment variable to override the options.
yices :: SMTSolver
yices = SMTSolver {
           name       = "Yices"
         , executable = "yices"
         -- , options    = ["-tc", "-smt", "-e"]   -- For Yices1
         , options    = ["-m", "-f"]  -- For Yices2
         , engine     = \cfg inps pgm -> do
                                execName <-                getEnv "SBV_YICES"           `catch` (\_ -> return (executable (solver cfg)))
                                execOpts <- (words `fmap` (getEnv "SBV_YICES_OPTIONS")) `catch` (\_ -> return (options (solver cfg)))
                                let cfg' = cfg { solver = (solver cfg) {executable = execName, options = execOpts} }
                                standardSolver cfg' pgm (ProofError cfg) (interpret cfg inps)
         }

timeout :: Int -> SMTSolver -> SMTSolver
timeout n s
  | n <= 0 = error $ "Yices.timeout value should be > 0, received: " ++ show n
  | True   = s{options = options s ++ ["-t", show n]}

sortByNodeId :: [(Int, a)] -> [(Int, a)]
sortByNodeId = sortBy (\(x, _) (y, _) -> compare x y)

interpret :: SMTConfig -> [NamedSymVar] -> [String] -> SMTResult
interpret cfg _    ("unsat":_)      = Unsatisfiable cfg
interpret cfg inps ("unknown":rest) = Unknown       cfg  $ extractMap inps rest
interpret cfg inps ("sat":rest)     = Satisfiable   cfg  $ extractMap inps rest
interpret cfg _    ("timeout":_)    = TimeOut       cfg
interpret cfg _    ls               = ProofError    cfg  $ ls

extractMap :: [NamedSymVar] -> [String] -> SMTModel
extractMap inps solverLines =
   SMTModel { modelAssocs    = map (\(_, y) -> y) $ sortByNodeId $ concatMap (getCounterExample inps) modelLines
            , modelUninterps = extractUnints unintLines
            }
  where (modelLines, unintLines) = break ("--- uninterpreted_" `isPrefixOf`) solverLines

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

extractUnints :: [String] -> [(String, [String])]
extractUnints [] = []
extractUnints xs = case extractUnint first of
                     Nothing -> extractUnints rest
                     Just x   -> x : extractUnints rest
  where first = takeWhile p xs
        rest  = tail' (dropWhile p xs)
        p = not . ("----" `isPrefixOf`)
        tail' []       = []
        tail' (_ : rs) = rs

extractUnint :: [String] -> Maybe (String, [String])
extractUnint []           = Nothing
extractUnint (tag : rest)
  | null tag' = Nothing
  | True      = foldM (getUIVal f) (0, []) rest >>= \(_, xs) -> return (f, reverse xs)
  where tag' = dropWhile (/= '_') tag
        f    = takeWhile (/= ' ') (tail tag')

getUIVal :: String -> (Int, [String]) -> String -> Maybe (Int, [String])
getUIVal f (cnt, sofar) s
  | "default: " `isPrefixOf` s
  = getDefaultVal cnt f (dropWhile (/= ' ') s) >>= \d -> return (cnt, d : sofar)
  | True
  = case parseSExpr s of
       Right (S_App [S_Con "=", (S_App (S_Con v : args)), S_Num i]) | v == "uninterpreted_" ++ f
              -> getCallVal cnt f args i >>= \(cnt', d) -> return (cnt', d : sofar)
       _ -> Nothing

getDefaultVal :: Int -> String -> String -> Maybe String
getDefaultVal cnt f n = case parseSExpr n of
                          Right (S_Num i) -> Just $ f ++ " " ++ unwords (replicate cnt "_") ++ " = " ++ show i
                          _               -> Nothing

getCallVal :: Int -> String -> [SExpr] -> Integer -> Maybe (Int, String)
getCallVal cnt f args res = mapM getArg args >>= \as -> return (cnt `max` length as, f ++ " " ++ unwords as ++ " = " ++ show res)

getArg :: SExpr -> Maybe String
getArg (S_Num i) = Just (show i)
getArg _         = Nothing
