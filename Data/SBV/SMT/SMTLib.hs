-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.SMT.SMTLib
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Conversion of symbolic programs to SMTLib format
-----------------------------------------------------------------------------

module Data.SBV.SMT.SMTLib(SMTLibPgm, SMTLibConverter, toSMTLib1, toSMTLib2, addNonEqConstraints, interpretSolverOutput) where

import Data.SBV.BitVectors.Data
import Data.SBV.SMT.SMT
import qualified Data.SBV.SMT.SMTLib1 as SMT1
import qualified Data.SBV.SMT.SMTLib2 as SMT2

type SMTLibConverter =  Bool                                        -- ^ is this a sat problem?
                     -> [String]                                    -- ^ extra comments to place on top
                     -> [(Quantifier, NamedSymVar)]                 -- ^ inputs and aliasing names
                     -> [Either SW (SW, [SW])]                      -- ^ skolemized inputs
                     -> [(SW, CW)]                                  -- ^ constants
                     -> [((Int, (Bool, Int), (Bool, Int)), [SW])]   -- ^ auto-generated tables
                     -> [(Int, ArrayInfo)]                          -- ^ user specified arrays
                     -> [(String, SBVType)]                         -- ^ uninterpreted functions/constants
                     -> [(String, [String])]                        -- ^ user given axioms
                     -> Pgm                                         -- ^ assignments
                     -> SW                                          -- ^ output variable
                     -> SMTLibPgm

toSMTLib1, toSMTLib2 :: SMTLibConverter
(toSMTLib1, toSMTLib2) = (cvt SMTLib1, cvt SMTLib2)
  where cvt v isSat comments qinps skolemMap consts tbls arrs uis axs asgnsSeq out = SMTLibPgm v (aliasTable, pre, post)
         where aliasTable  = map (\(_, (x, y)) -> (y, x)) qinps
               converter   = if v == SMTLib1 then SMT1.cvt else SMT2.cvt
               (pre, post) = converter isSat comments qinps skolemMap consts tbls arrs uis axs asgnsSeq out

addNonEqConstraints :: [(Quantifier, NamedSymVar)] -> [[(String, CW)]] -> SMTLibPgm -> Maybe String
addNonEqConstraints _qinps cs p@(SMTLibPgm SMTLib1 _) = SMT1.addNonEqConstraints cs p
addNonEqConstraints  qinps cs p@(SMTLibPgm SMTLib2 _) = SMT2.addNonEqConstraints qinps cs p

interpretSolverOutput :: SMTConfig -> ([String] -> SMTModel) -> [String] -> SMTResult
interpretSolverOutput cfg _          ("unsat":_)      = Unsatisfiable cfg
interpretSolverOutput cfg extractMap ("unknown":rest) = Unknown       cfg  $ extractMap rest
interpretSolverOutput cfg extractMap ("sat":rest)     = Satisfiable   cfg  $ extractMap rest
interpretSolverOutput cfg _          ("timeout":_)    = TimeOut       cfg
interpretSolverOutput cfg _          ls               = ProofError    cfg  ls
