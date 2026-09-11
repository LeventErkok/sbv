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
  , adtCType
  , arrayKindTag
  , arrayOutputCTypeName
  , arrayStoredCloneName
  , arrayStoredReleaseName
  , tupleFieldName
  , elementCType
  , kindTag
  ) where

import Data.Char                   (isAlphaNum, isAscii, ord)
import Numeric                     (showHex)

import Data.SBV.Compilers.C.FP         (arbitraryFPCType)
import Data.SBV.Core.Data

-- | Return the public C structure type used for a tuple kind.
tupleCType :: Kind -> String
tupleCType kind@KTuple{} = "SBVTuple_" ++ kindTag kind
tupleCType kind          = error $ "SBV->C: Expected a tuple kind, received " ++ show kind

-- | Return the public C structure type used for a concrete ADT kind or an
-- unresolved application of a registered ADT.
adtCType :: Kind -> String
adtCType kind@(KADT typeName parameters _)
  | isADT kind && not (isRoundingMode kind) && not (isUninterpreted kind)
  = appliedType typeName (map snd parameters)
  | True
  = error $ "SBV->C: Expected a concrete ADT kind, received " ++ show kind
adtCType (KApp typeName arguments) = appliedType typeName arguments
adtCType kind = error $ "SBV->C: Expected an ADT kind, received " ++ show kind

-- | Render the common C type spelling shared by a concrete ADT and an
-- unresolved application of that same registered ADT.
appliedType :: String -> [Kind] -> String
appliedType typeName arguments = "SBVADT_" ++ encodeIdentifier typeName ++ concatMap parameterTag arguments
 where parameterTag parameterKind = "_" ++ show (length tag) ++ "_" ++ tag
        where tag = kindTag parameterKind

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
elementCType kind@KADT{}
  | isRoundingMode kind          = "RoundingMode"
  | True                         = adtCType kind
elementCType kind@KApp{}         = adtCType kind
elementCType (KList elementKind) = "SBVList_" ++ kindTag elementKind
elementCType (KSet elementKind)  = "SBVSet_" ++ kindTag elementKind
elementCType kind@KArray{}       = arrayOutputCTypeName kind ++ " *"
elementCType kind                = error $ "SBV->C: Unsupported structural kind: " ++ show kind

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
kindTag kind@KADT{}
  | isRoundingMode kind     = "rounding_mode"
  | True                    = "adt_" ++ encodeIdentifier (adtCType kind)
kindTag kind@KApp{}         = "adt_" ++ encodeIdentifier (adtCType kind)
kindTag (KList elementKind) = "list_" ++ taggedKind (kindTag elementKind)
kindTag (KSet elementKind)  = "set_"  ++ taggedKind (kindTag elementKind)
kindTag kind@KArray{}       = "array_" ++ taggedKind (arrayKindTag kind)
kindTag kind                = error $ "SBV->C: Unsupported structural kind: " ++ show kind

-- | Return the key/value suffix shared by generated names for an array kind.
arrayKindTag :: Kind -> String
arrayKindTag (KArray keyKind valueKind) = kindTag keyKind ++ "_" ++ kindTag valueKind
arrayKindTag kind                       = error $ "SBV->C: Expected an array kind, received " ++ show kind

-- | Return the public owned-output descriptor name for an array kind.
arrayOutputCTypeName :: Kind -> String
arrayOutputCTypeName kind@KArray{} = "SBVArrayOutput_" ++ arrayKindTag kind
arrayOutputCTypeName kind          = error $ "SBV->C: Expected an array kind, received " ++ show kind

-- | Return the helper name that clones an array descriptor stored by pointer
-- inside another generated value.
arrayStoredCloneName :: Kind -> String
arrayStoredCloneName kind@KArray{} = "sbv_array_stored_clone_" ++ arrayKindTag kind
arrayStoredCloneName kind          = error $ "SBV->C: Expected an array kind, received " ++ show kind

-- | Return the helper name that releases an array descriptor stored by pointer
-- inside another generated value.
arrayStoredReleaseName :: Kind -> String
arrayStoredReleaseName kind@KArray{} = "sbv_array_stored_release_" ++ arrayKindTag kind
arrayStoredReleaseName kind          = error $ "SBV->C: Expected an array kind, received " ++ show kind

-- | Prefix a generated kind tag with its length so adjacent tags cannot
-- collide.
taggedKind :: String -> String
taggedKind value = show (length value) ++ "_" ++ value

-- | Encode an arbitrary Haskell type name as a valid C identifier component.
encodeIdentifier :: String -> String
encodeIdentifier = concatMap encode
 where encode character
         | isAscii character && isAlphaNum character = [character]
         | True                                      = "_x" ++ showHex (ord character) "" ++ "_"
