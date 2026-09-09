-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.Tuple
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Structural tuple lowering for the SBV-to-C compiler.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.Tuple
  ( tupleKinds
  , tupleCType
  , tupleFieldName
  , tupleTypeDecls
  , tupleValue
  , tupleConst
  , tupleExpr
  , tupleUsesExact
  ) where

import Data.Char                       (toUpper)
import Data.List                       (nub, sortOn)
import qualified Data.Set as Set

import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as P ((<>))

import Data.SBV.Compilers.C.FP         (arbitraryFPCType)
import Data.SBV.Compilers.C.GMP        (isExactGMPKind)
import Data.SBV.Compilers.C.Lowering   (CLowering, CStorage(..), expressionLowering)
import Data.SBV.Compilers.CodeGen      (CgConfig)
import Data.SBV.Core.Data
import Data.SBV.Core.Kind              (expandKinds)

-- | Return the distinct tuple kinds used by a program, with nested tuple
-- declarations ordered before the structures that contain them.
tupleKinds :: Set.Set Kind -> [Kind]
tupleKinds = sortOn tupleDepth . nub . concatMap (filter isTuple . expandKinds) . Set.toAscList
 where tupleDepth :: Kind -> Int
       tupleDepth (KTuple fields) = 1 + maximum (0 : map tupleDepth fields)
       tupleDepth _               = 0

-- | Return the public C structure type used for a tuple kind.
tupleCType :: Kind -> String
tupleCType kind@KTuple{} = "SBVTuple_" ++ kindTag kind
tupleCType kind          = error $ "SBV->C: Expected a tuple kind, received " ++ show kind

-- | Emit public structure declarations for all tuple kinds used by a program.
-- The unit tuple carries a private byte because ISO C does not permit empty
-- structures.
tupleTypeDecls :: [Kind] -> Doc
tupleTypeDecls []     = empty
tupleTypeDecls tuples = text . unlines $ "/* Structural tuple values. */" : concatMap declaration tuples
 where declaration kind@(KTuple fields) =
            [ "#ifndef " ++ tupleGuard kind
            , "#define " ++ tupleGuard kind
            , "typedef struct {"
            ]
         ++ (case fields of
               [] -> ["  uint8_t unit;"]
               _  -> zipWith fieldDeclaration [1 :: Int ..] fields)
         ++ [ "} " ++ tupleCType kind ++ ";"
            , "#endif"
            , ""
            ]
       declaration kind = error $ "SBV->C: Expected a tuple kind, received " ++ show kind

       fieldDeclaration index kind = "  " ++ elementCType kind ++ " " ++ tupleFieldName index ++ ";"

-- | Render a concrete tuple value as a C99 compound literal.
tupleConst :: (CV -> Doc) -> CV -> Maybe Doc
tupleConst renderValue (CV kind@(KTuple fieldKinds) (CTuple fieldValues))
  | length fieldKinds == length fieldValues
  = Just $ tupleValue kind (zipWith (\fieldKind fieldValue -> renderValue (CV fieldKind fieldValue)) fieldKinds fieldValues)
  | True
  = error $ "SBV->C: Malformed tuple constant " ++ show (CV kind (CTuple fieldValues))
tupleConst _ _ = Nothing

-- | Lower tuple construction, projection, conditionals, and labels. Other
-- operators are left to the scalar pipeline; SBV normally expands structural
-- comparisons into field operations before code generation.
tupleExpr :: CgConfig -> Op -> [SV] -> Kind -> [Doc] -> Maybe CLowering
tupleExpr cfg op svs resultKind args
  | not (isTuple resultKind || any isTuple svs)
  = Nothing
  | True
  = case (op, svs, args) of
      (TupleConstructor arity, fields, renderedFields)
        | KTuple fieldKinds <- resultKind
        , arity == length fieldKinds
        , map kindOf fields == fieldKinds
        -> lower resultKind $ tupleValue resultKind renderedFields
      (TupleAccess fieldIndex arity, [tupleSV], [renderedTuple])
        | KTuple fieldKinds <- kindOf tupleSV
        , arity == length fieldKinds
        , fieldIndex >= 1
        , fieldIndex <= arity
        , resultKind == fieldKinds !! (fieldIndex - 1)
        -> lower resultKind $ parens renderedTuple P.<> text "." P.<> text (tupleFieldName fieldIndex)
      (Ite, [_condition, left, right], [renderedCondition, renderedLeft, renderedRight])
        | resultKind == kindOf left
        , resultKind == kindOf right
        -> lower resultKind $ renderedCondition <+> text "?" <+> renderedLeft <+> text ":" <+> renderedRight
      (Label label, [_], [renderedTuple])
        -> lower resultKind $ renderedTuple <+> text "/*" <+> text label <+> text "*/"
      _ -> Nothing
 where lower kind = Just . expressionLowering storage []
        where storage
                | tupleUsesExact cfg kind = CFunctionScoped
                | True                    = CByValue

-- | Test whether a tuple contains an exact GMP-backed integer or real at any
-- nesting depth under the active code-generation configuration.
tupleUsesExact :: CgConfig -> Kind -> Bool
tupleUsesExact cfg = any (isExactGMPKind cfg) . expandKinds

-- | Render a tuple expression from its field expressions.
tupleValue :: Kind -> [Doc] -> Doc
tupleValue kind@(KTuple []) [] = parens (text (tupleCType kind)) P.<> braces (text "0")
tupleValue kind@(KTuple fieldKinds) fields
  | length fieldKinds == length fields
  = parens (text (tupleCType kind)) P.<> braces (fsep (punctuate comma designatedFields))
  | True
  = error $ "SBV->C: Tuple literal field mismatch for " ++ show kind
 where designatedFields = zipWith (\index field -> text "." P.<> text (tupleFieldName index) <+> text "=" <+> field) [1 :: Int ..] fields
tupleValue kind _ = error $ "SBV->C: Expected a tuple kind, received " ++ show kind

-- | Return the public member name used for a one-based tuple field index.
tupleFieldName :: Int -> String
tupleFieldName index
  | index >= 1 = "field" ++ show index
  | True       = error $ "SBV->C: Tuple fields are one-based, received " ++ show index

-- | Return the public C type used for one tuple field.
elementCType :: Kind -> String
elementCType KBool               = "SBool"
elementCType (KBounded False 1)  = "SBool"
elementCType (KBounded False w)  = "SWord" ++ show w
elementCType (KBounded True  w)  = "SInt" ++ show w
elementCType KUnbounded          = "SInteger"
elementCType KReal               = "SReal"
elementCType KFloat              = "SFloat"
elementCType KDouble             = "SDouble"
elementCType kind@KFP{}          = arbitraryFPCType kind
elementCType kind@KTuple{}       = tupleCType kind
elementCType kind
  | isRoundingMode kind = "RoundingMode"
  | True                = error $ "SBV->C: Unsupported tuple field kind: " ++ show kind

-- | Return the collision-free suffix used by a generated tuple type.
kindTag :: Kind -> String
kindTag KBool              = "u1"
kindTag (KBounded False w) = "u" ++ show w
kindTag (KBounded True  w) = "s" ++ show w
kindTag KUnbounded         = "integer"
kindTag KReal              = "real"
kindTag KFloat             = "float"
kindTag KDouble            = "double"
kindTag (KFP eb sb)        = "fp_e" ++ show eb ++ "_s" ++ show sb
kindTag (KTuple fields)    = "t" ++ show (length fields) ++ concatMap (('_' :) . taggedKind . kindTag) fields
kindTag kind
  | isRoundingMode kind = "rounding_mode"
  | True                = error $ "SBV->C: Unsupported tuple field kind: " ++ show kind

-- | Prefix a generated kind tag with its length so adjacent tags cannot
-- collide.
taggedKind :: String -> String
taggedKind value = show (length value) ++ "_" ++ value

-- | Return the preprocessor guard protecting one tuple declaration.
tupleGuard :: Kind -> String
tupleGuard kind = map toUpper (tupleCType kind) ++ "_DEFINED"
