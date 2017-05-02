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

module Data.SBV.SMT.SMTLib(
          SMTLibPgm
        , SMTLibConverter
        , toSMTLib2
        , addNonEqConstraints
        , interpretSolverOutput
        , interpretSolverModelLine
        , interpretSolverObjectiveLine
        ) where

import Data.Char (isDigit)

import Data.SBV.Core.Data
import Data.SBV.Provers.SExpr
import qualified Data.SBV.SMT.SMTLib2 as SMT2
import qualified Data.Set as Set (Set, member, toList)

-- | An instance of SMT-Lib converter; instantiated for SMT-Lib v1 and v2. (And potentially for newer versions in the future.)
type SMTLibConverter =  Set.Set Kind                 -- ^ Kinds used in the problem
                     -> Bool                         -- ^ is this a sat problem?
                     -> [String]                     -- ^ extra comments to place on top
                     -> [(Quantifier, NamedSymVar)]  -- ^ inputs and aliasing names
                     -> [Either SW (SW, [SW])]       -- ^ skolemized inputs
                     -> [(SW, CW)]                   -- ^ constants
                     -> [((Int, Kind, Kind), [SW])]  -- ^ auto-generated tables
                     -> [(Int, ArrayInfo)]           -- ^ user specified arrays
                     -> [(String, SBVType)]          -- ^ uninterpreted functions/constants
                     -> [(String, [String])]         -- ^ user given axioms
                     -> SBVPgm                       -- ^ assignments
                     -> [SW]                         -- ^ extra constraints
                     -> SW                           -- ^ output variable
                     -> SMTConfig                    -- ^ configuration
                     -> CaseCond                     -- ^ case analysis
                     -> SMTLibPgm

-- | Convert to SMTLib-2 format
toSMTLib2 :: SMTLibConverter
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
               converter    = case v of
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

-- | Add constraints generated from older models, used for querying new models
addNonEqConstraints :: SMTLibVersion -> RoundingMode -> [(Quantifier, NamedSymVar)] -> [[(String, CW)]] -> Maybe [String]
addNonEqConstraints SMTLib2 = SMT2.addNonEqConstraints

-- | Interpret solver output based on SMT-Lib standard output responses
interpretSolverOutput :: SMTConfig -> ([String] -> SMTModel) -> [String] -> SMTResult
interpretSolverOutput cfg _          ("unsat":_)      = Unsatisfiable cfg
interpretSolverOutput cfg extractMap ("unknown":rest) = Unknown       cfg  $ extractMap rest
interpretSolverOutput cfg extractMap ("sat":rest)     = let m = extractMap rest
                                                        in case filter (not . isRegularCW . snd) (modelObjectives m) of
                                                                 [] -> Satisfiable cfg m
                                                                 _  -> SatExtField cfg m
interpretSolverOutput cfg _          ("timeout":_)    = TimeOut       cfg
interpretSolverOutput cfg _          ls               = ProofError    cfg  ls

-- | Get a counter-example from an SMT-Lib2 like model output line
-- This routing is necessarily fragile as SMT solvers tend to print output
-- in whatever form they deem convenient for them.. Currently, it's tuned to
-- work with Z3 and CVC4; if new solvers are added, we might need to rework
-- the logic here.
interpretSolverModelLine :: [NamedSymVar] -> String -> [(Int, (String, CW))]
interpretSolverModelLine inps line = either err (modelValues True inps line) (parseSExpr line)
  where err r =  error $  "*** Failed to parse SMT-Lib2 model output from: "
                       ++ "*** " ++ show line ++ "\n"
                       ++ "*** Reason: " ++ r ++ "\n"

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
modelValues errOnUnrecognized inps line = extract
  where getInput = identifyInput inps

        getUIIndex (KUserSort  _ (Right xs)) i = i `lookup` zip xs [0..]
        getUIIndex _                         _ = Nothing

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
                go e                                                = die "extract" e

                die w r = error $   "SBV.SMTLib: Cannot " ++ w ++ " objective value from solver output!"
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
                         cvt e = die "convert" e

                -- drop the pesky to_real's that Z3 produces.. Cool but useless.
                simplify :: SExpr -> SExpr
                simplify (EApp [ECon "to_real", n]) = n
                simplify (EApp xs)                  = EApp (map simplify xs)
                simplify e                          = e

{-# ANN modelValues  ("HLint: ignore Use elemIndex" :: String) #-}
