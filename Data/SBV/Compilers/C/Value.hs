-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.Value
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Shared properties and operations for structurally lowered C values.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.Value
  ( valueNeedsOwnership
  , byValueEqual
  ) where

import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as P ((<>))

import Data.SBV.Compilers.C.BV         (isWideBV, wideBVEqual)
import Data.SBV.Compilers.C.FP         (arbitraryFPEqual, arbitraryFPObjectEqual, nativeFPObjectEqual)
import Data.SBV.Compilers.C.GMP        (gmpEqual, isExactGMPKind)
import Data.SBV.Compilers.C.Types      (tupleFieldName)
import Data.SBV.Compilers.CodeGen      (CgConfig)
import Data.SBV.Core.Data

-- | Test whether a value requires clone-and-release ownership when it crosses
-- a generated C ABI boundary. ADT ownership is resolved separately because it
-- depends on the complete registered type graph.
valueNeedsOwnership :: CgConfig -> Kind -> Bool
valueNeedsOwnership cfg kind
  | isExactGMPKind cfg kind = True
valueNeedsOwnership _   KString        = True
valueNeedsOwnership _   KList{}        = True
valueNeedsOwnership _   KSet{}         = True
valueNeedsOwnership cfg (KTuple kinds) = any (valueNeedsOwnership cfg) kinds
valueNeedsOwnership _   _              = False

-- | Render equality for a scalar or recursively nested by-value tuple. The
-- Boolean flag selects object equality for floating-point values.
byValueEqual :: CgConfig -> Bool -> Kind -> Doc -> Doc -> Doc
byValueEqual cfg strong kind left right
  | isWideBV kind                              = wideBVEqual kind left right
  | isFP kind && strong                        = arbitraryFPObjectEqual kind left right
  | isFP kind                                  = arbitraryFPEqual kind left right
  | strong && (isFloat kind || isDouble kind) = nativeFPObjectEqual left right
  | isExactGMPKind cfg kind                    = gmpEqual kind left right
  | KTuple fields <- kind                      = tupleEquality fields
  | True                                       = left <+> text "==" <+> right
 where tupleEquality fields = parens . fsep . punctuate (text " &&") $
         zipWith equalField [1 :: Int ..] fields

       equalField index fieldKind = byValueEqual cfg strong fieldKind
         (parens left  P.<> text "." P.<> text (tupleFieldName index))
         (parens right P.<> text "." P.<> text (tupleFieldName index))
