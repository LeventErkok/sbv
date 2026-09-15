-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.Legacy
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Compatibility facade for the original SBV-to-C compiler.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.Legacy
  ( compileToC
  , compileToCLib
  , compileToC'
  , compileToCLib'
  ) where

import Data.SBV.Compilers.C.Legacy.Internal (compileToC, compileToC', compileToCLib, compileToCLib')
