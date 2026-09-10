-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.Types
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Shared C type names for structurally lowered SBV kinds.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.Types
  ( tupleCType
  , tupleFieldName
  , elementCType
  , kindTag
  ) where

import Data.SBV.Compilers.C.FP (arbitraryFPCType)
import Data.SBV.Core.Data

-- | Return the public C structure type used for a tuple kind.
tupleCType :: Kind -> String
tupleCType kind@KTuple{} = "SBVTuple_" ++ kindTag kind
tupleCType kind          = error $ "SBV->C: Expected a tuple kind, received " ++ show kind

-- | Return the public member name used for a one-based tuple field index.
tupleFieldName :: Int -> String
tupleFieldName index
  | index >= 1 = "field" ++ show index
  | True       = error $ "SBV->C: Tuple fields are one-based, received " ++ show index

-- | Return the public C type used for a structurally lowered field or element.
elementCType :: Kind -> String
elementCType KBool               = "SBool"
elementCType (KBounded False 1)  = "SBool"
elementCType (KBounded False w)  = "SWord" ++ show w
elementCType (KBounded True  w)  = "SInt" ++ show w
elementCType KUnbounded          = "SInteger"
elementCType KReal               = "SReal"
elementCType KRational           = "SRational"
elementCType KFloat              = "SFloat"
elementCType KDouble             = "SDouble"
elementCType KChar               = "SChar"
elementCType KString             = "SString"
elementCType kind@KFP{}          = arbitraryFPCType kind
elementCType kind@KTuple{}       = tupleCType kind
elementCType (KList elementKind) = "SBVList_" ++ kindTag elementKind
elementCType (KSet elementKind)  = "SBVSet_" ++ kindTag elementKind
elementCType kind
  | isRoundingMode kind = "RoundingMode"
  | True                = error $ "SBV->C: Unsupported structural kind: " ++ show kind

-- | Return the collision-free suffix used by a generated structural C type.
kindTag :: Kind -> String
kindTag KBool               = "u1"
kindTag (KBounded False w)  = "u" ++ show w
kindTag (KBounded True  w)  = "s" ++ show w
kindTag KUnbounded          = "integer"
kindTag KReal               = "real"
kindTag KRational           = "rational"
kindTag KFloat              = "float"
kindTag KDouble             = "double"
kindTag KChar               = "char"
kindTag KString             = "string"
kindTag (KFP eb sb)         = "fp_e" ++ show eb ++ "_s" ++ show sb
kindTag (KTuple fields)     = "t" ++ show (length fields) ++ concatMap (('_' :) . taggedKind . kindTag) fields
kindTag (KList elementKind) = "list_" ++ taggedKind (kindTag elementKind)
kindTag (KSet elementKind)  = "set_"  ++ taggedKind (kindTag elementKind)
kindTag kind
  | isRoundingMode kind = "rounding_mode"
  | True                = error $ "SBV->C: Unsupported structural kind: " ++ show kind

-- | Prefix a generated kind tag with its length so adjacent tags cannot
-- collide.
taggedKind :: String -> String
taggedKind value = show (length value) ++ "_" ++ value
