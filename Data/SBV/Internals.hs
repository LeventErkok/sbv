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
  Result(..), SBVRunMode(..)
  -- * Internal structures useful for low-level programming
  , module Data.SBV.Core.Data
  -- * Operations useful for instantiating SBV type classes
  , genLiteral, genFromCW, genMkSymVar, checkAndConvert, genParse, showModel, SMTModel(..), liftQRem, liftDMod
  -- * Polynomial operations that operate on bit-vectors
  , ites, mdp, addPoly
  -- * Compilation to C
  , compileToC', compileToCLib'
  -- * Code generation primitives
  , module Data.SBV.Compilers.CodeGen
  -- * Various math utilities around floats
  , module Data.SBV.Utils.Numeric
  ) where

import Data.SBV.Core.Data
import Data.SBV.Core.Model      (genLiteral, genFromCW, genMkSymVar)
import Data.SBV.Core.Splittable (checkAndConvert)
import Data.SBV.Core.Model      (liftQRem, liftDMod)

import Data.SBV.Compilers.C       (compileToC', compileToCLib')
import Data.SBV.Compilers.CodeGen

import Data.SBV.SMT.SMT (genParse, showModel)

import Data.SBV.Tools.Polynomial      (ites, mdp, addPoly)
import Data.SBV.Utils.Numeric

{-# ANN module ("HLint: ignore Use import/export shortcut" :: String) #-}
