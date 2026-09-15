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
  , tupleForwardTypeDecls
  , tupleTypeDecls
  , tupleOwnershipTypeDecls
  , tupleOwnedInitName
  , tupleOwnedSetName
  , tupleOwnedCloneName
  , tupleOwnedReleaseName
  , tupleDriverInit
  , tupleValue
  , tupleConst
  , tupleExpr
  , tupleUsesExact
  , tupleNeedsOwnership
  , elementCType
  , kindTag
  ) where

import Data.List                       (nub, sortOn)
import qualified Data.Set as Set

import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as P ((<>))

import Data.SBV.Compilers.C.Array      (arrayStoredLoad, arrayStoredValue)
import Data.SBV.Compilers.C.GMP        (gmpFunctionName, gmpOutputType, isExactGMPKind)
import Data.SBV.Compilers.C.List       (listClone, listRelease)
import Data.SBV.Compilers.C.Lowering   (CLowering, expressionLowering)
import Data.SBV.Compilers.C.Set        (setClone, setRelease)
import Data.SBV.Compilers.C.Syntax     (cCommentText)
import Data.SBV.Compilers.C.Types      (elementCType, kindTag, tupleCType, tupleFieldName)
import Data.SBV.Compilers.C.Value      (managedValueClone, managedValueRelease, valueDriverInit, valueNeedsOwnership)
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

-- | Emit forward declarations that permit collection descriptors to refer to
-- tuple element types before their layouts are complete.
tupleForwardTypeDecls :: [Kind] -> Doc
tupleForwardTypeDecls []     = empty
tupleForwardTypeDecls tuples = text . unlines $ "/* Forward declarations for structural tuples. */" : concatMap declaration tuples
 where declaration kind@KTuple{} =
         [ "#ifndef " ++ tupleForwardGuard kind
         , "#define " ++ tupleForwardGuard kind
         , "typedef struct " ++ tupleCType kind ++ " " ++ tupleCType kind ++ ";"
         , "#endif"
         , ""
         ]
       declaration kind = error $ "SBV->C: Expected a tuple kind, received " ++ show kind

-- | Emit public structure definitions for all tuple kinds used by a program.
-- The unit tuple carries a private byte because ISO C does not permit empty
-- structures. Each definition also provides its own guarded forward
-- declaration so this function remains independently usable.
tupleTypeDecls :: [Kind] -> Doc
tupleTypeDecls []     = empty
tupleTypeDecls tuples = text . unlines $ "/* Structural tuple values. */" : concatMap declaration tuples
 where declaration kind@(KTuple fields) =
            [ "#ifndef " ++ tupleGuard kind
            , "#define " ++ tupleGuard kind
            , "#ifndef " ++ tupleForwardGuard kind
            , "#define " ++ tupleForwardGuard kind
            , "typedef struct " ++ tupleCType kind ++ " " ++ tupleCType kind ++ ";"
            , "#endif"
            , "struct " ++ tupleCType kind ++ " {"
            ]
         ++ (case fields of
               [] -> ["  uint8_t unit;"]
               _  -> zipWith fieldDeclaration [1 :: Int ..] fields)
         ++ [ "};"
            , "#endif"
            , ""
            ]
       declaration kind = error $ "SBV->C: Expected a tuple kind, received " ++ show kind

       fieldDeclaration index kind = "  " ++ elementCType kind ++ " " ++ tupleFieldName index ++ ";"

-- | Emit public ownership helpers for tuples containing exact GMP-backed,
-- string, collection, retained-array, or concrete ADT fields. Inputs may
-- borrow an ordinary tuple value.
-- Cloned values own their recursively managed fields and must be released
-- with 'tupleOwnedReleaseName'.
tupleOwnershipTypeDecls :: CgConfig -> [Kind] -> Doc
tupleOwnershipTypeDecls cfg tuples
  | null owned = empty
  | True       = text . unlines $ concatMap declaration owned
 where owned = filter (tupleNeedsOwnership cfg) tuples

       declaration kind@(KTuple fields) =
          [ "#ifndef " ++ ownershipGuard
          , "#define " ++ ownershipGuard
          , "/* Recursive ownership helpers for " ++ tupleCType kind ++ ". */"
          , "/* Owned values have unique ownership; clone before copying and release every owner. */"
          , "static inline SBV_CGEN_UNUSED void " ++ tupleOwnedInitName kind ++ "(" ++ tupleCType kind ++ " *value)"
          , "{"
          , "  if (value == NULL) abort();"
          , "  memset(value, 0, sizeof *value);"
          ]
          ++ concat (zipWith initializeField [1 :: Int ..] fields)
          ++ [ "}"
          , ""
          , "static inline SBV_CGEN_UNUSED void " ++ tupleOwnedSetName kind ++ "(" ++ tupleCType kind ++ " *target, " ++ tupleCType kind ++ " source)"
          , "{"
          ]
          ++ concat (zipWith setField [1 :: Int ..] fields)
          ++ [ "}"
          , ""
          , "static inline SBV_CGEN_UNUSED " ++ tupleCType kind ++ " " ++ tupleOwnedCloneName kind ++ "(" ++ tupleCType kind ++ " source)"
          , "{"
          , "  " ++ tupleCType kind ++ " result;"
          , "  " ++ tupleOwnedInitName kind ++ "(&result);"
          , "  " ++ tupleOwnedSetName kind ++ "(&result, source);"
          , "  return result;"
          , "}"
          , ""
          , "static inline SBV_CGEN_UNUSED void " ++ tupleOwnedReleaseName kind ++ "(" ++ tupleCType kind ++ " *value)"
          , "{"
          , "  if (value == NULL) return;"
          ]
          ++ concat (zipWith releaseField [1 :: Int ..] fields)
          ++ [ "  memset(value, 0, sizeof *value);"
          , "}"
          , "#endif"
          , ""
         ]
         where ownershipGuard = tupleCType kind ++ "_OWNERSHIP_DEFINED"

               initializeField index fieldKind
                  | isExactGMPKind cfg fieldKind
                  = let access  = "value->" ++ tupleFieldName index
                        mutable = gmpOutputType fieldKind
                        local   = "field" ++ show index
                    in [ "  " ++ mutable ++ " " ++ local ++ " = (" ++ mutable ++ ") malloc(sizeof(*" ++ local ++ "));"
                       , "  if (" ++ local ++ " == NULL) abort();"
                       , "  " ++ gmpFunctionName fieldKind "init" ++ "(" ++ local ++ ");"
                       , "  " ++ access ++ " = " ++ local ++ ";"
                       ]
                  | fieldKind == KString
                  = ["  value->" ++ tupleFieldName index ++ " = (SString) {NULL, 0, 0};"]
                  | isList fieldKind
                  = ["  value->" ++ tupleFieldName index ++ " = (" ++ elementCType fieldKind ++ ") {NULL, 0};"]
                  | isSet fieldKind
                  = ["  value->" ++ tupleFieldName index ++ " = (" ++ elementCType fieldKind ++ ") {NULL, 0, false};"]
                  | isArray fieldKind
                  = ["  value->" ++ tupleFieldName index ++ " = NULL;"]
                  | isTuple fieldKind && tupleNeedsOwnership cfg fieldKind
                  = ["  " ++ tupleOwnedInitName fieldKind ++ "(&value->" ++ tupleFieldName index ++ ");"]
                  | True
                  = []

               setField index fieldKind
                  | isExactGMPKind cfg fieldKind
                  = ["  " ++ gmpFunctionName fieldKind "set" ++ "((" ++ gmpOutputType fieldKind ++ ") target->" ++ field ++ ", source." ++ field ++ ");"]
                  | fieldKind == KString
                  = [ "  const SString " ++ field ++ "_copy = sbv_string_clone(source." ++ field ++ ");"
                    , "  sbv_string_release(&target->" ++ field ++ ");"
                    , "  target->" ++ field ++ " = " ++ field ++ "_copy;"
                    ]
                  | isList fieldKind
                  = [ "  const " ++ elementCType fieldKind ++ " " ++ field ++ "_copy = " ++ render (listClone fieldKind (text ("source." ++ field))) ++ ";"
                    , "  " ++ render (listRelease fieldKind (text ("target->" ++ field)))
                    , "  target->" ++ field ++ " = " ++ field ++ "_copy;"
                    ]
                  | isSet fieldKind
                  = [ "  const " ++ elementCType fieldKind ++ " " ++ field ++ "_copy = " ++ render (setClone fieldKind (text ("source." ++ field))) ++ ";"
                    , "  " ++ render (setRelease fieldKind (text ("target->" ++ field)))
                    , "  target->" ++ field ++ " = " ++ field ++ "_copy;"
                    ]
                  | isArray fieldKind
                  = [ "  " ++ elementCType fieldKind ++ " " ++ field ++ "_copy = " ++ render (managedValueClone fieldKind (text ("source." ++ field))) ++ ";"
                    , "  " ++ render (managedValueRelease fieldKind (text ("&target->" ++ field)))
                    , "  target->" ++ field ++ " = " ++ field ++ "_copy;"
                    ]
                  | isTuple fieldKind && tupleNeedsOwnership cfg fieldKind
                  = ["  " ++ tupleOwnedSetName fieldKind ++ "(&target->" ++ field ++ ", source." ++ field ++ ");"]
                  | valueNeedsOwnership cfg fieldKind
                  = [ "  " ++ elementCType fieldKind ++ " " ++ field ++ "_copy = " ++ render (managedValueClone fieldKind (text ("source." ++ field))) ++ ";"
                    , "  " ++ render (managedValueRelease fieldKind (text ("&target->" ++ field)))
                    , "  target->" ++ field ++ " = " ++ field ++ "_copy;"
                    ]
                  | True
                  = ["  target->" ++ field ++ " = source." ++ field ++ ";"]
                  where field = tupleFieldName index

               releaseField index fieldKind
                  | isExactGMPKind cfg fieldKind
                  = [ "  if (value->" ++ field ++ " != NULL) {"
                    , "    " ++ gmpFunctionName fieldKind "clear" ++ "((" ++ gmpOutputType fieldKind ++ ") value->" ++ field ++ ");"
                    , "    free((void *) value->" ++ field ++ ");"
                    , "  }"
                    ]
                  | fieldKind == KString
                  = ["  sbv_string_release(&value->" ++ field ++ ");"]
                  | isList fieldKind
                  = ["  " ++ render (listRelease fieldKind (text ("value->" ++ field)))]
                  | isSet fieldKind
                  = ["  " ++ render (setRelease fieldKind (text ("value->" ++ field)))]
                  | isArray fieldKind
                  = ["  " ++ render (managedValueRelease fieldKind (text ("&value->" ++ field)))]
                  | isTuple fieldKind && tupleNeedsOwnership cfg fieldKind
                  = ["  " ++ tupleOwnedReleaseName fieldKind ++ "(&value->" ++ field ++ ");"]
                  | valueNeedsOwnership cfg fieldKind
                  = ["  " ++ render (managedValueRelease fieldKind (text ("&value->" ++ field)))]
                  | True
                  = []
                  where field = tupleFieldName index
       declaration kind = error $ "SBV->C: Expected a tuple kind, received " ++ show kind

-- | Return the helper name that initializes caller-owned storage for a tuple
-- with recursively managed fields.
tupleOwnedInitName :: Kind -> String
tupleOwnedInitName kind = "sbv_tuple_owned_init_" ++ kindTag kind

-- | Return the helper name that assigns into initialized owned tuple storage.
tupleOwnedSetName :: Kind -> String
tupleOwnedSetName kind = "sbv_tuple_owned_set_" ++ kindTag kind

-- | Return the public helper name that deep-copies a managed-field tuple.
tupleOwnedCloneName :: Kind -> String
tupleOwnedCloneName kind = "sbv_tuple_owned_clone_" ++ kindTag kind

-- | Return the public helper name that releases an owned managed-field tuple.
tupleOwnedReleaseName :: Kind -> String
tupleOwnedReleaseName kind = "sbv_tuple_owned_release_" ++ kindTag kind

-- | Initialize a generated-driver tuple and populate its fields from a seed.
-- Recursively owned fields use the public owned-tuple storage protocol; other
-- fields use the supplied scalar renderer. Array and ADT fields delegate to
-- the supplied statement initializer.
tupleDriverInit :: CgConfig -> (Kind -> Integer -> Doc) -> (Kind -> String -> Integer -> Doc) -> Kind -> String -> Integer -> Doc
tupleDriverInit cfg renderValue initializeValue kind@KTuple{} externalName seed = valueDriverInit cfg renderValue initializeValue kind externalName seed
tupleDriverInit _   _           _               kind         _            _    = error $ "SBV->C: Expected a tuple kind, received " ++ show kind

-- | Render a concrete tuple value as a C99 compound literal.
tupleConst :: (CV -> Doc) -> CV -> Maybe Doc
tupleConst renderValue (CV kind@(KTuple fieldKinds) (CTuple fieldValues))
  | length fieldKinds == length fieldValues
  = Just $ tupleValue kind (zipWith (\fieldKind fieldValue -> arrayStoredValue fieldKind (renderValue (CV fieldKind fieldValue))) fieldKinds fieldValues)
  | True
  = error $ "SBV->C: Malformed tuple constant " ++ show (CV kind (CTuple fieldValues))
tupleConst _ _ = Nothing

-- | Lower tuple construction, projection, conditionals, and labels. Other
-- operators are left to the scalar pipeline; SBV normally expands structural
-- comparisons into field operations before code generation.
tupleExpr :: Op -> [SV] -> SV -> [Doc] -> Maybe CLowering
tupleExpr op svs resultSV args
  | not (isTuple resultKind || any isTuple svs)
  = Nothing
  | True
  = case (op, svs, args) of
      (TupleConstructor arity, fields, renderedFields)
        | KTuple fieldKinds <- resultKind
        , arity == length fieldKinds
        , map kindOf fields == fieldKinds
        -> lower $ tupleValue resultKind (zipWith arrayStoredValue fieldKinds renderedFields)
      (TupleAccess fieldIndex arity, [tupleSV], [renderedTuple])
        | KTuple fieldKinds <- kindOf tupleSV
        , arity == length fieldKinds
        , fieldIndex >= 1
        , fieldIndex <= arity
        , resultKind == fieldKinds !! (fieldIndex - 1)
        -> let field = parens renderedTuple P.<> text "." P.<> text (tupleFieldName fieldIndex)
           in if isArray resultKind then Just (arrayStoredLoad resultSV field) else lower field
      (Label label, [_], [renderedTuple])
        -> lower $ renderedTuple <+> text "/*" <+> cCommentText label <+> text "*/"
      _ -> Nothing
 where resultKind = kindOf resultSV

       lower = Just . expressionLowering []

-- | Test whether a tuple contains an exact GMP-backed integer, real, or
-- rational at any nesting depth under the active code-generation configuration.
tupleUsesExact :: CgConfig -> Kind -> Bool
tupleUsesExact cfg kind@KTuple{} = any (isExactGMPKind cfg) (expandKinds kind)
tupleUsesExact _   _             = False

-- | Test whether a tuple contains a field that must be cloned when it crosses
-- the generated function's ownership boundary.
tupleNeedsOwnership :: CgConfig -> Kind -> Bool
tupleNeedsOwnership cfg kind@KTuple{} = valueNeedsOwnership cfg kind
tupleNeedsOwnership _   _             = False

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

-- | Return the preprocessor guard protecting one tuple definition.
tupleGuard :: Kind -> String
tupleGuard kind = tupleCType kind ++ "_DEFINED"

-- | Return the preprocessor guard protecting one tuple forward declaration.
tupleForwardGuard :: Kind -> String
tupleForwardGuard kind = tupleCType kind ++ "_FORWARD_DEFINED"
