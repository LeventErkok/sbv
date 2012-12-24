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

module Data.SBV.SMT.SMTLib(SMTLibPgm, SMTLibConverter, toSMTLib1, toSMTLib2, addNonEqConstraints, interpretSolverOutput, interpretSolverModelLine) where

import Data.Char (isDigit)

import Data.SBV.BitVectors.Data
import Data.SBV.SMT.SMT
import Data.SBV.Provers.SExpr
import qualified Data.SBV.SMT.SMTLib1 as SMT1
import qualified Data.SBV.SMT.SMTLib2 as SMT2

-- | An instance of SMT-Lib converter; instantiated for SMT-Lib v1 and v2. (And potentially for
-- newer versions in the future.)
type SMTLibConverter =  (Bool, Bool)                -- ^ has unbounded integers/reals
                     -> Maybe String                 -- ^ set-logic string to use in case not automatically determined (if any)
                     -> Bool                        -- ^ is this a sat problem?
                     -> [String]                    -- ^ extra comments to place on top
                     -> [String]                    -- ^ uninterpreted sorts
                     -> [(Quantifier, NamedSymVar)] -- ^ inputs and aliasing names
                     -> [Either SW (SW, [SW])]      -- ^ skolemized inputs
                     -> [(SW, CW)]                  -- ^ constants
                     -> [((Int, Kind, Kind), [SW])] -- ^ auto-generated tables
                     -> [(Int, ArrayInfo)]          -- ^ user specified arrays
                     -> [(String, SBVType)]         -- ^ uninterpreted functions/constants
                     -> [(String, [String])]        -- ^ user given axioms
                     -> SBVPgm                      -- ^ assignments
                     -> [SW]                        -- ^ extra constraints
                     -> SW                          -- ^ output variable
                     -> SMTLibPgm

-- | Convert to SMTLib-1 format
toSMTLib1 :: SMTLibConverter

-- | Convert to SMTLib-2 format
toSMTLib2 :: SMTLibConverter
(toSMTLib1, toSMTLib2) = (cvt SMTLib1, cvt SMTLib2)
  where cvt v mbDefaultLogic boundedInfo isSat comments sorts qinps skolemMap consts tbls arrs uis axs asgnsSeq cstrs out = SMTLibPgm v (aliasTable, pre, post)
         where aliasTable  = map (\(_, (x, y)) -> (y, x)) qinps
               converter   = if v == SMTLib1 then SMT1.cvt else SMT2.cvt
               (pre, post) = converter mbDefaultLogic boundedInfo isSat comments sorts qinps skolemMap consts tbls arrs uis axs asgnsSeq cstrs out

-- | Add constraints generated from older models, used for querying new models
addNonEqConstraints :: [(Quantifier, NamedSymVar)] -> [[(String, CW)]] -> SMTLibPgm -> Maybe String
addNonEqConstraints _qinps cs p@(SMTLibPgm SMTLib1 _) = SMT1.addNonEqConstraints cs p
addNonEqConstraints  qinps cs p@(SMTLibPgm SMTLib2 _) = SMT2.addNonEqConstraints qinps cs p

-- | Interpret solver output based on SMT-Lib standard output responses
interpretSolverOutput :: SMTConfig -> ([String] -> SMTModel) -> [String] -> SMTResult
interpretSolverOutput cfg _          ("unsat":_)      = Unsatisfiable cfg
interpretSolverOutput cfg extractMap ("unknown":rest) = Unknown       cfg  $ extractMap rest
interpretSolverOutput cfg extractMap ("sat":rest)     = Satisfiable   cfg  $ extractMap rest
interpretSolverOutput cfg _          ("timeout":_)    = TimeOut       cfg
interpretSolverOutput cfg _          ls               = ProofError    cfg  ls

-- | Get a counter-example from an SMT-Lib2 like model output line
-- This routing is necessarily fragile as SMT solvers tend to print output
-- in whatever form they deem convenient for them.. Currently, it's tuned to
-- work with Z3 and CVC4; if new solvers are added, we might need to rework
-- the logic here.
interpretSolverModelLine :: [NamedSymVar] -> String -> [(Int, (String, CW))]
interpretSolverModelLine inps line = either err extract (parseSExpr line)
  where err r =  error $  "*** Failed to parse SMT-Lib2 model output from: "
                       ++ "*** " ++ show line ++ "\n"
                       ++ "*** Reason: " ++ r ++ "\n"
        getInput (SCon v)            = isInput v
        getInput (SApp (SCon v : _)) = isInput v
        getInput _                   = Nothing
        isInput ('s':v)
          | all isDigit v = let inpId :: Int
                                inpId = read v
                            in case [(s, nm) | (s@(SW _ (NodeId n)), nm) <-  inps, n == inpId] of
                                 []        -> Nothing
                                 [(s, nm)] -> Just (inpId, s, nm)
                                 matches -> error $  "SBV.SMTLib2: Cannot uniquely identify value for "
                                                  ++ 's':v ++ " in "  ++ show matches
        isInput _       = Nothing
        extract (SApp [SApp [v, SNum i]])  | Just (n, s, nm) <- getInput v = [(n, (nm, mkConstCW (kindOf s) i))]
        extract (SApp [SApp [v, SReal i]]) | Just (n, _, nm) <- getInput v = [(n, (nm, CW KReal      (CWAlgReal i)))]
        extract (SApp [SApp [v, SCon i]])  | Just (n, s, nm) <- getInput v = [(n, (nm, CW (kindOf s) (CWUninterpreted i)))]
        -- weird lambda app that CVC4 seems to throw out.. logic below derived from what I saw CVC4 print, hopefully sufficient
        extract (SApp (SApp (v : SApp (SCon "LAMBDA" : xs) : _) : _)) | Just{} <- getInput v, not (null xs) = extract (SApp [SApp [v, last xs]])
        extract (SApp [SApp (v : r)])      | Just (_, _, nm) <- getInput v = error $   "SBV.SMTLib2: Cannot extract value for " ++ show nm
                                                                                   ++ "\n\tInput: " ++ show line
                                                                                   ++ "\n\tParse: " ++  show r
        extract _                                                          = []
