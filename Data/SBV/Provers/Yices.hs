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

import Data.Char          (isDigit)
import Data.List          (sortBy, isPrefixOf, intercalate, transpose, partition)
import Data.Maybe         (catMaybes, isJust, fromJust)
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
         , engine     = \cfg inps modelMap pgm -> do
                                execName <-                getEnv "SBV_YICES"           `catch` (\_ -> return (executable (solver cfg)))
                                execOpts <- (words `fmap` (getEnv "SBV_YICES_OPTIONS")) `catch` (\_ -> return (options (solver cfg)))
                                let cfg' = cfg { solver = (solver cfg) {executable = execName, options = execOpts} }
                                standardSolver cfg' pgm (ProofError cfg) (interpret cfg inps modelMap)
         }

timeout :: Int -> SMTSolver -> SMTSolver
timeout n s
  | n <= 0 = error $ "Yices.timeout value should be > 0, received: " ++ show n
  | True   = s{options = options s ++ ["-t", show n]}

sortByNodeId :: [(Int, a)] -> [(Int, a)]
sortByNodeId = sortBy (\(x, _) (y, _) -> compare x y)

interpret :: SMTConfig -> [NamedSymVar] -> [(String, UnintKind)] -> [String] -> SMTResult
interpret cfg _    _        ("unsat":_)      = Unsatisfiable cfg
interpret cfg inps modelMap ("unknown":rest) = Unknown       cfg  $ extractMap inps modelMap rest
interpret cfg inps modelMap ("sat":rest)     = Satisfiable   cfg  $ extractMap inps modelMap rest
interpret cfg _    _        ("timeout":_)    = TimeOut       cfg
interpret cfg _    _        ls               = ProofError    cfg  $ ls

extractMap :: [NamedSymVar] -> [(String, UnintKind)] -> [String] -> SMTModel
extractMap inps modelMap solverLines =
   SMTModel { modelAssocs    = map (\(_, y) -> y) $ sortByNodeId $ concatMap (getCounterExample inps) modelLines
            , modelUninterps = [(n, ls) | (UFun _ n, ls) <- uis]
            , modelArrays    = [(n, ls) | (UArr _ n, ls) <- uis]
            }
  where (modelLines, unintLines) = moveConstUIs $ break ("--- " `isPrefixOf`) solverLines
        uis = extractUnints modelMap unintLines

-- another crude hack
moveConstUIs :: ([String], [String]) -> ([String], [String])
moveConstUIs (pre, post) = (pre', concatMap mkDecl extras ++ post)
  where (extras, pre') = partition ("(= uninterpreted_" `isPrefixOf`) pre
        mkDecl s = ["--- " ++ takeWhile (/= ' ') (drop 3 s) ++ " ---", s]

getCounterExample :: [NamedSymVar] -> String -> [(Int, (String, CW))]
getCounterExample inps line = either err extract (parseSExpr line)
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

extractUnints :: [(String, UnintKind)] -> [String] -> [(UnintKind, [String])]
extractUnints modelMap = catMaybes . map (extractUnint modelMap) . chunks
  where chunks []     = []
        chunks (x:xs) = let (f, r) = span (not . ("---" `isPrefixOf`)) xs in (x:f) : chunks r

-- Parsing the Yices output is done extremely crudely and designed
-- mostly by observation of Yices output. Likely to have bugs and
-- brittle as Yices evolves. We really need an SMT-Lib2 like interface.
extractUnint :: [(String, UnintKind)] -> [String] -> Maybe (UnintKind, [String])
extractUnint _    []           = Nothing
extractUnint mmap (tag : rest)
  | null tag'                  = Nothing
  | not (isJust mbKnd)         = Nothing
  | True                       = mapM (getUIVal knd) rest >>= \xs -> return (knd, format knd xs)
  where mbKnd | "--- uninterpreted_" `isPrefixOf` tag = uf `lookup` mmap
              | True                                  = af `lookup` mmap
        knd = fromJust mbKnd
        tag' = dropWhile (/= '_') tag
        f    = takeWhile (/= ' ') (tail tag')
        uf   = f
        af   = "array_" ++ f

getUIVal :: UnintKind -> String -> Maybe (String, [String], String)
getUIVal knd s
  | "default: " `isPrefixOf` s
  = getDefaultVal knd (dropWhile (/= ' ') s)
  | True
  = case parseSExpr s of
       Right (S_App [S_Con "=", (S_App (S_Con _ : args)), S_Num i]) -> getCallVal knd args i
       Right (S_App [S_Con "=", S_Con _, S_Num i])                  -> getCallVal knd []   i
       _ -> Nothing

getDefaultVal :: UnintKind -> String -> Maybe (String, [String], String)
getDefaultVal knd n = case parseSExpr n of
                        Right (S_Num i) -> Just $ showDefault knd (show i)
                        _               -> Nothing

getCallVal :: UnintKind -> [SExpr] -> Integer -> Maybe (String, [String], String)
getCallVal knd args res = mapM getArg args >>= \as -> return (showCall knd as (show res))

getArg :: SExpr -> Maybe String
getArg (S_Num i) = Just (show i)
getArg _         = Nothing

showDefault :: UnintKind -> String -> (String, [String], String)
showDefault (UFun cnt f) res = (f, replicate cnt "_", res)
showDefault (UArr cnt f) res = (f, replicate cnt "_", res)

showCall :: UnintKind -> [String] -> String -> (String, [String], String)
showCall (UFun _ f) as res = (f, as, res)
showCall (UArr _ f) as res = (f, as, res)

format :: UnintKind -> [(String, [String], String)] -> [String]
format (UFun{}) eqns = fmtFun eqns
format (UArr{}) eqns = let fmt (f, as, r) = f ++ "[" ++ intercalate ", " as ++ "] = " ++ r in map fmt eqns

fmtFun :: [(String, [String], String)] -> [String]
fmtFun ls = map fmt ls
  where fmt (f, as, r) = f ++ " " ++ unwords (map align (zip as (lens ++ repeat 0))) ++ " = " ++ r
        lens           = map (maximum . (0:)) $ map (map length) $ transpose [as | (_, as, _) <- ls]
        align (s, i)   = take (i `max` length s) (s ++ repeat ' ')
