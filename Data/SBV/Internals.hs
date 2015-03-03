---------------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Internals
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Low level functions to access the SBV infrastructure, for developers who
-- want to build further tools on top of SBV. End-users of the library
-- should not need to use this module.
---------------------------------------------------------------------------------

module Data.SBV.Internals (
  -- * Running symbolic programs /manually/
  Result, SBVRunMode(..), runSymbolic, runSymbolic'
  -- * Other internal structures useful for low-level programming
  , SBV(..), slet, CW(..), Kind(..), CWVal(..), AlgReal(..), Quantifier(..), mkConstCW, genVar, genVar_
  , liftQRem, liftDMod, symbolicMergeWithKind
  , cache, sbvToSW, newExpr, normCW, SBVExpr(..), Op(..), mkSymSBVWithRandom
  , SBVType(..), newUninterpreted, forceSWArg
  -- * Operations useful for instantiating SBV type classes
  , genLiteral, genFromCW, genMkSymVar, checkAndConvert, genParse
  -- * Polynomial operations that operate on bit-vectors
  , ites, mdp, addPoly
  -- * Compilation to C
  , compileToC', compileToCLib', CgPgmBundle(..), CgPgmKind(..)
  ) where

import Data.SBV.BitVectors.Data       (Result, SBVRunMode(..), runSymbolic, runSymbolic', SBV(..), CW(..), Kind(..), CWVal(..), AlgReal(..), Quantifier(..), mkConstCW)
import Data.SBV.BitVectors.Data       (cache, sbvToSW, newExpr, normCW, SBVExpr(..), Op(..), mkSymSBVWithRandom, SBVType(..), newUninterpreted, forceSWArg)
import Data.SBV.BitVectors.Model      (genVar, genVar_, slet, liftQRem, liftDMod, symbolicMergeWithKind, genLiteral, genFromCW, genMkSymVar)
import Data.SBV.BitVectors.Splittable (checkAndConvert)
import Data.SBV.Compilers.C           (compileToC', compileToCLib')
import Data.SBV.Compilers.CodeGen     (CgPgmBundle(..), CgPgmKind(..))
import Data.SBV.SMT.SMT               (genParse)
import Data.SBV.Tools.Polynomial      (ites, mdp, addPoly)
