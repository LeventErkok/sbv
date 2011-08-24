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

module Data.SBV.Provers.Z3_QBVF(qbvfSolver, z3) where

import System.Environment (getEnv)

import Data.SBV.BitVectors.Data
import Data.SBV.SMT.SMT
import Data.SBV.SMT.SMTLib(SMTLibPgm(..))

z3 :: SMTSolver
z3 = SMTSolver {
           name       = "z3"
         , executable = "z3"
         , options    = ["/smt2", "/m", "/in"]
         , engine     = \cfg _inps _modelMap pgm -> do
                                execName <-                getEnv "SBV_Z3"           `catch` (\_ -> return (executable (solver cfg)))
                                execOpts <- (words `fmap` (getEnv "SBV_Z3_OPTIONS")) `catch` (\_ -> return (options (solver cfg)))
                                let cfg' = cfg { solver = (solver cfg) {executable = execName, options = execOpts} }
                                standardSolver cfg' pgm (ProofError cfg) (ProofError cfg)
         }

qbvfSolver :: Bool                                        -- ^ is this a sat problem?
           -> [String]                                    -- ^ extra comments to place on top
           -> [(Quantifier, (SW, String))]                -- ^ inputs and aliasing names
           -> [(SW, CW)]                                  -- ^ constants
           -> [((Int, (Bool, Int), (Bool, Int)), [SW])]   -- ^ auto-generated tables
           -> [(Int, ArrayInfo)]                          -- ^ user specified arrays
           -> [(String, SBVType)]                         -- ^ uninterpreted functions/constants
           -> [(String, [String])]                        -- ^ user given axioms
           -> Pgm                                         -- ^ assignments
           -> SW                                          -- ^ output variable
           -> SMTLibPgm
qbvfSolver _isSat _comments qinps _consts _tbls _arrs _uis _axs _asgnsSeq _out
  | not (needsExistentials (map fst qinps))
  = error "qbvf: There are no existentials in this problem for QBVF solving. Use 'sat', or 'prove' instead."
  | True
  = SMTLibPgm ([], [], [ "(assert (exists ((x (_ BitVec 16))) (forall ((y (_ BitVec 16))) (bvuge y x))))"
                       , "(check-sat)"
                       , "(get-model)"
                       ])
