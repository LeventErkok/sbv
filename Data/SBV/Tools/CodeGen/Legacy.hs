-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.CodeGen.Legacy
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Opt-in access to the original SBV-to-C compiler. This module exports the
-- same code-generation interface as "Data.SBV.Tools.CodeGen"; changing the
-- import is sufficient to select the compatibility backend.
--
-- @
-- import Data.SBV.Tools.CodeGen.Legacy
-- @
--
-- New code should normally import "Data.SBV.Tools.CodeGen" instead.
-- Native real-to-integer flooring uses the same overflow-safe, low-bit mapping
-- as the current backend; flooring a non-finite mapped real fails explicitly.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.CodeGen.Legacy
  ( module Data.SBV.Tools.CodeGen
  , compileToC
  , compileToCLib
  ) where

import Data.SBV.Compilers.C.Legacy (compileToC, compileToCLib)
import Data.SBV.Tools.CodeGen hiding (compileToC, compileToCLib)
