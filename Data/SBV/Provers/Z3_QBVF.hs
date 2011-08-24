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

module Data.SBV.Provers.Z3_QBVF(qbvfSolver) where

import Data.SBV.BitVectors.Data
import Data.SBV.SMT.SMT

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
           -> IO QBVFResult
qbvfSolver _isSat _comments qinps _consts _tbls _arrs _uis _axs _asgnsSeq _out
  | not (needsExistentials (map fst qinps))
  = error "qbvf: There are no existentials in this problem for QBVF solving. Use 'sat', or 'prove' instead."
  | True
  = error "qbvf: TBD"
