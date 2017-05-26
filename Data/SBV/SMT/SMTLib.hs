-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.SMT.SMTLib
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Conversion of symbolic programs to SMTLib format
-----------------------------------------------------------------------------

{-# LANGUAGE NamedFieldPuns #-}

module Data.SBV.SMT.SMTLib (
          SMTLibPgm
        , toSMTLib
        , toIncSMTLib
        , addNonEqConstraints
        , interpretSolverOutput
        , interpretSolverOutputMulti
        , interpretSolverModelLine
        , interpretSolverObjectiveLine
        ) where

import Data.Char  (isDigit)
import Data.Maybe (isJust, fromJust)

import qualified Data.Set as Set (member, toList)

import Data.SBV.Core.Data
import Data.SBV.Utils.SExpr

import Data.SBV.SMT.Utils
import qualified Data.SBV.SMT.SMTLib2 as SMT2

toSMTLib :: SMTConfig -> SMTLibConverter SMTLibPgm
toSMTLib SMTConfig{smtLibVersion} = case smtLibVersion of
                                      SMTLib2 -> toSMTLib2

toIncSMTLib :: SMTConfig -> SMTLibIncConverter [String]
toIncSMTLib SMTConfig{smtLibVersion} = case smtLibVersion of
                                         SMTLib2 -> toIncSMTLib2

-- | Convert to SMTLib-2 format
toSMTLib2 :: SMTLibConverter SMTLibPgm
toSMTLib2 = cvt SMTLib2
  where cvt v kindInfo isSat comments qinps skolemMap consts tbls arrs uis axs asgnsSeq cstrs out config caseSelectors
         | KUnbounded `Set.member` kindInfo && not (supportsUnboundedInts solverCaps)
         = unsupported "unbounded integers"
         | KReal `Set.member` kindInfo  && not (supportsReals solverCaps)
         = unsupported "algebraic reals"
         | needsFloats && not (supportsFloats solverCaps)
         = unsupported "single-precision floating-point numbers"
         | needsDoubles && not (supportsDoubles solverCaps)
         = unsupported "double-precision floating-point numbers"
         | needsQuantifiers && not (supportsQuantifiers solverCaps)
         = unsupported "quantifiers"
         | not (null sorts) && not (supportsUninterpretedSorts solverCaps)
         = unsupported "uninterpreted sorts"
         | needsOptimization && not (supportsOptimization solverCaps)
         = unsupported "optimization routines"
         | not $ null needsUniversalOpt
         = unsupportedAll $ "optimization of universally quantified metric(s): " ++ unwords needsUniversalOpt
         | True
         = SMTLibPgm v pgm
         where sorts = [s | KUserSort s _ <- Set.toList kindInfo]
               solverCaps = capabilities (solver config)
               unsupported w = error $ unlines [ "SBV: Given problem needs " ++ w
                                               , "*** Which is not supported by SBV for the chosen solver: " ++ capSolverName solverCaps
                                               ]
               unsupportedAll w = error $ unlines [ "SBV: Given problem needs " ++ w
                                                  , "*** Which is not supported by SBV."
                                                  ]
               converter = case v of
                             SMTLib2 -> SMT2.cvt
               pgm = converter kindInfo isSat comments qinps skolemMap consts tbls arrs uis axs asgnsSeq cstrs out config caseSelectors

               needsFloats  = KFloat  `Set.member` kindInfo
               needsDoubles = KDouble `Set.member` kindInfo
               (needsOptimization, needsUniversalOpt) = case caseSelectors of
                                                          Opt ss -> let universals   = [s | (ALL, (s, _)) <- qinps]
                                                                        check (x, y) = any (`elem` universals) [x, y]
                                                                        isUniversal (Maximize nm xy) | check xy = [nm]
                                                                        isUniversal (Minimize nm xy) | check xy = [nm]
                                                                        isUniversal _                           = []
                                                                    in  (True,  concatMap isUniversal ss)
                                                          _      -> (False, [])
               needsQuantifiers
                 | isSat = ALL `elem` quantifiers
                 | True  = EX  `elem` quantifiers
                 where quantifiers = map fst qinps

-- | Convert to SMTLib-2 format
toIncSMTLib2 :: SMTLibIncConverter [String]
toIncSMTLib2 = cvt SMTLib2
  where cvt SMTLib2 = SMT2.cvtInc

-- | Add constraints generated from older models, used for querying new models
addNonEqConstraints :: SMTLibVersion -> RoundingMode -> [(Quantifier, NamedSymVar)] -> [[(String, CW)]] -> Maybe [String]
addNonEqConstraints SMTLib2 = SMT2.addNonEqConstraints

-- | Interpret solver output based on SMT-Lib standard output responses
interpretSolverOutput :: SMTConfig -> ([String] -> SMTModel) -> [String] -> SMTResult
interpretSolverOutput cfg _          ("unsat":ucCore) = Unsatisfiable cfg $ parseUnsatCore (getUnsatCore cfg) ucCore
interpretSolverOutput cfg extractMap ("unknown":rest) = Unknown       cfg $ extractMap rest
interpretSolverOutput cfg extractMap ("sat":rest)     = classifyModel cfg $ extractMap rest
interpretSolverOutput cfg _          ("timeout":_)    = TimeOut       cfg
interpretSolverOutput cfg _          ls               = ProofError    cfg ls

-- | Parse unsat-core if requested
parseUnsatCore :: Bool -> [String] -> Maybe [String]
parseUnsatCore False _  = Nothing
parseUnsatCore True  ls = Just $ concatMap getLabels ls
   where getLabels s = case parseSExpr s of
                         Left  e         -> bad e
                         Right (EApp xs) -> let result = map grab xs
                                            in if all isJust result
                                               then map fromJust result
                                               else bad "Unexpected non-label construct"
                         Right _         -> bad "Unexpected response from the solver"

          where grab (ECon l) = Just $ noBar l
                grab _        = Nothing

                noBar = reverse . dropWhile bar . reverse . dropWhile bar
                bar   = (== '|')

                bad e = error $ unlines [ "SBV: Cannot extract an unsat core:"
                                        , "  Received:  " ++ show s
                                        , "  Reason  : " ++ e
                                        ]

-- | Do we have a regular sat-model, or something in the extension field?
classifyModel :: SMTConfig -> SMTModel -> SMTResult
classifyModel cfg m = case filter (not . isRegularCW . snd) (modelObjectives m) of
                        [] -> Satisfiable cfg m
                        _  -> SatExtField cfg m

-- | Interpret solver output based on SMT-Lib standard output responses, in the case we're expecting multiple objective model values
interpretSolverOutputMulti :: Int -> SMTConfig -> ([String] -> SMTModel) -> [String] -> [SMTResult]
interpretSolverOutputMulti n cfg extractMap outLines
   | degenerate
   = replicate n $ interpretSolverOutput cfg extractMap preModels
   | n /= lms
   = error $ "SBV: Expected " ++ show n ++ " models, received: " ++ show lms ++ ":\n" ++ unlines outLines
   | True
   = map (interpretSolverOutput cfg extractMap) multiModels
  where degenerate = case outLines of
                      ("sat"    :_) -> False
                      ("unknown":_) -> False
                      _             -> True

        (preModels, postModels) = case break (== "(sbv_objective_model_marker)") outLines of
                                    (pre, _:post) -> (pre, post)
                                    r             -> r

        walk [] sofar = reverse sofar
        walk xs sofar = case break (== "(sbv_objective_model_marker)") xs of
                          (g, [])     -> walk []   (g:sofar)
                          (g, _:rest) -> walk rest (g:sofar)

        multiModels = map (preModels ++) (walk postModels [])
        lms         = length multiModels

-- | Get a counter-example from an SMT-Lib2 like model output line
-- This routing is necessarily fragile as SMT solvers tend to print output
-- in whatever form they deem convenient for them.. Currently, it's tuned to
-- work with Z3 and CVC4; if new solvers are added, we might need to rework
-- the logic here.
interpretSolverModelLine :: [NamedSymVar] -> String -> [(Int, (String, CW))]
interpretSolverModelLine inps line = either parseError chkErr (parseSExpr line)
  where parseError r =  error $  unlines [ ""
                                         , "*** Failed to parse SMT-Lib2 model output from: "
                                         , "*** " ++ show line ++ "\n"
                                         , "*** Reason: " ++ r ++ "\n"
                                         ]

        solverError e = error $  unlines [ ""
                                         , "*** Cannot extract model values."
                                         , "***   Solver says: " ++ e
                                         , "*** Make sure models are queried in a sat-context"
                                         , "*** That is, after a checkSat call returning a Sat result."
                                         ]

        chkErr e = case e of
                    EApp [ECon "error", ECon er] -> solverError er
                    _                            -> modelValues True inps line e

identifyInput :: [NamedSymVar] -> SExpr -> Maybe (Int, SW, String)
identifyInput inps = classify
  where classify (ECon v)            = isInput v
        classify (EApp (ECon v : _)) = isInput v
        classify _                   = Nothing

        isInput ('s':v)
          | all isDigit v = let inpId :: Int
                                inpId = read v
                            in case [(s, nm) | (s@(SW _ (NodeId n)), nm) <-  inps, n == inpId] of
                                 []        -> Nothing
                                 [(s, nm)] -> Just (inpId, s, nm)
                                 matches -> error $  "SBV.SMTLib: Cannot uniquely identify value for "
                                                  ++ 's':v ++ " in "  ++ show matches
        isInput _       = Nothing

-- | Turn an sexpr to a binding in our model
modelValues :: Bool -> [NamedSymVar] -> String -> SExpr -> [(Int, (String, CW))]
modelValues errOnUnrecognized inps line = extractModel
  where getInput = identifyInput inps

        getUIIndex (KUserSort  _ (Right xs)) i = i `lookup` zip xs [0..]
        getUIIndex _                         _ = Nothing

        -- Lines of the form (model (define-fun s0 () Int 0) ...)
        extractModel (EApp (ECon "model" : rest)) = concatMap extractDefine rest
        extractModel e                            = extract e

        -- Lines of the form (define-fun s0 () Int 0)
        extractDefine (EApp (ECon "define-fun" : nm : EApp [] : ECon _ : rest)) = extract $ EApp [EApp (nm : rest)]
        extractDefine r = error $   "SBV.SMTLib: Cannot extract value from model level define-fun:"
                                ++ "\n\tInput: " ++ show line
                                ++ "\n\tParse: " ++ show r

        -- Lines of the form ((s0 0))
        extract (EApp [EApp [v, ENum    i]]) | Just (n, s, nm) <- getInput v                    = [(n, (nm, mkConstCW (kindOf s) (fst i)))]
        extract (EApp [EApp [v, EReal   i]]) | Just (n, s, nm) <- getInput v, isReal s          = [(n, (nm, CW KReal (CWAlgReal i)))]

        -- the following is when z3 returns a cast to an int. Inherently dangerous! (but useful)
        extract (EApp [EApp [v, EReal   i]]) | Just (n, _, nm) <- getInput v                    = [(n, (nm, CW KReal (CWAlgReal i)))]

        extract (EApp [EApp [v, ECon    i]]) | Just (n, s, nm) <- getInput v, isUninterpreted s = let k = kindOf s in [(n, (nm, CW k (CWUserSort (getUIIndex k i, i))))]
        extract (EApp [EApp [v, EDouble i]]) | Just (n, s, nm) <- getInput v, isDouble s        = [(n, (nm, CW KDouble (CWDouble i)))]
        extract (EApp [EApp [v, EFloat  i]]) | Just (n, s, nm) <- getInput v, isFloat s         = [(n, (nm, CW KFloat (CWFloat i)))]

        -- weird lambda app that CVC4 seems to throw out.. logic below derived from what I saw CVC4 print, hopefully sufficient
        extract (EApp (EApp (v : EApp (ECon "LAMBDA" : xs) : _) : _)) | Just{} <- getInput v, not (null xs) = extract (EApp [EApp [v, last xs]])

        extract (EApp [EApp (v : r)])
          | Just (_, _, nm) <- getInput v
          , errOnUnrecognized
          = error $   "SBV.SMTLib: Cannot extract value for " ++ show nm
                   ++ "\n\tInput: " ++ show line
                   ++ "\n\tParse: " ++ show r

        extract _ = []

-- | Similar to reading model-lines but designed for reading objectives.
interpretSolverObjectiveLine :: [NamedSymVar] -> String -> [(Int, (String, GeneralizedCW))]
interpretSolverObjectiveLine inps line = either err extract (parseSExpr line)
  where err r =  error $  "*** Failed to parse SMT-Lib2 model output from: "
                       ++ "*** " ++ show line ++ "\n"
                       ++ "*** Reason: " ++ r ++ "\n"

        getInput = identifyInput inps

        extract :: SExpr -> [(Int, (String, GeneralizedCW))]
        extract (EApp (ECon "objectives" : es)) = concatMap getObjValue es
        extract _                               = []

        getObjValue :: SExpr -> [(Int, (String, GeneralizedCW))]
        getObjValue e = case modelValues False inps line (EApp [e]) of
                          [] -> getUnboundedValues e
                          xs -> [(i, (s, RegularCW v)) | (i, (s, v)) <- xs]

        getUnboundedValues :: SExpr -> [(Int, (String, GeneralizedCW))]
        getUnboundedValues item = go item
          where go (EApp [v, rest]) | Just (n, s, nm) <- getInput v = [(n, (nm, ExtendedCW (toGenCW (kindOf s) (simplify rest))))]
                go _                                                = []

                die r = error $   "SBV.SMTLib: Cannot convert objective value from solver output!"
                             ++ "\n\tInput     : " ++ show line
                             ++ "\n\tParse     : " ++ show r
                             ++ "\n\tItem Parse: " ++ show item

                -- Convert to an extended expression. Hopefully complete!
                toGenCW :: Kind -> SExpr -> ExtCW
                toGenCW k = cvt
                   where cvt (ECon "oo")                    = Infinite  k
                         cvt (ECon "epsilon")               = Epsilon   k
                         cvt (EApp [ECon "interval", x, y]) = Interval  (cvt x) (cvt y)
                         cvt (ENum    (i, _))               = BoundedCW $ mkConstCW k i
                         cvt (EReal   r)                    = BoundedCW $ CW k $ CWAlgReal r
                         cvt (EFloat  f)                    = BoundedCW $ CW k $ CWFloat   f
                         cvt (EDouble d)                    = BoundedCW $ CW k $ CWDouble  d
                         cvt (EApp [ECon "+", x, y])        = AddExtCW (cvt x) (cvt y)
                         cvt (EApp [ECon "*", x, y])        = MulExtCW (cvt x) (cvt y)
                         -- Nothing else should show up, hopefully!
                         cvt e = die e

                -- drop the pesky to_real's that Z3 produces.. Cool but useless.
                simplify :: SExpr -> SExpr
                simplify (EApp [ECon "to_real", n]) = n
                simplify (EApp xs)                  = EApp (map simplify xs)
                simplify e                          = e

{-# ANN modelValues  ("HLint: ignore Use elemIndex" :: String) #-}
