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
  , elementCType
  , kindTag
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

-- | Emit public ownership helpers for tuples containing exact GMP-backed
-- fields. Inputs may borrow an ordinary tuple value. Cloned values own their
-- exact fields and must be released with 'tupleOwnedReleaseName'.
tupleOwnershipTypeDecls :: CgConfig -> [Kind] -> Doc
tupleOwnershipTypeDecls cfg tuples
  | null owned = empty
  | True       = text . unlines $ concatMap declaration owned
 where owned = filter (tupleUsesExact cfg) tuples

       declaration kind@(KTuple fields) =
          [ "#ifndef " ++ ownershipGuard
          , "#define " ++ ownershipGuard
          , "/* Owned exact-field helpers for " ++ tupleCType kind ++ ". */"
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
         where ownershipGuard = map toUpper (tupleCType kind) ++ "_OWNERSHIP_DEFINED"

               initializeField index fieldKind
                  | isExactGMPKind cfg fieldKind
                  = let access  = "value->" ++ tupleFieldName index
                        mutable = exactMutableType fieldKind
                        local   = "field" ++ show index
                    in [ "  " ++ mutable ++ " " ++ local ++ " = (" ++ mutable ++ ") malloc(sizeof(*" ++ local ++ "));"
                       , "  if (" ++ local ++ " == NULL) abort();"
                       , "  " ++ exactInit fieldKind ++ "(" ++ local ++ ");"
                       , "  " ++ access ++ " = " ++ local ++ ";"
                       ]
                  | isTuple fieldKind && tupleUsesExact cfg fieldKind
                  = ["  " ++ tupleOwnedInitName fieldKind ++ "(&value->" ++ tupleFieldName index ++ ");"]
                  | True
                  = []

               setField index fieldKind
                  | isExactGMPKind cfg fieldKind
                  = ["  " ++ exactSet fieldKind ++ "((" ++ exactMutableType fieldKind ++ ") target->" ++ field ++ ", source." ++ field ++ ");"]
                  | isTuple fieldKind && tupleUsesExact cfg fieldKind
                  = ["  " ++ tupleOwnedSetName fieldKind ++ "(&target->" ++ field ++ ", source." ++ field ++ ");"]
                  | True
                  = ["  target->" ++ field ++ " = source." ++ field ++ ";"]
                  where field = tupleFieldName index

               releaseField index fieldKind
                  | isExactGMPKind cfg fieldKind
                  = [ "  if (value->" ++ field ++ " != NULL) {"
                    , "    " ++ exactClear fieldKind ++ "((" ++ exactMutableType fieldKind ++ ") value->" ++ field ++ ");"
                    , "    free((void *) value->" ++ field ++ ");"
                    , "  }"
                    ]
                  | isTuple fieldKind && tupleUsesExact cfg fieldKind
                  = ["  " ++ tupleOwnedReleaseName fieldKind ++ "(&value->" ++ field ++ ");"]
                  | True
                  = []
                  where field = tupleFieldName index
       declaration kind = error $ "SBV->C: Expected a tuple kind, received " ++ show kind

       exactMutableType KUnbounded = "mpz_ptr"
       exactMutableType fieldKind
         | isExactGMPKind cfg fieldKind = "mpq_ptr"
       exactMutableType kind       = error $ "SBV->C: Expected an exact tuple field, received " ++ show kind

       exactInit KUnbounded = "mpz_init"
       exactInit fieldKind
         | isExactGMPKind cfg fieldKind = "mpq_init"
       exactInit kind       = error $ "SBV->C: Expected an exact tuple field, received " ++ show kind

       exactSet KUnbounded = "mpz_set"
       exactSet fieldKind
         | isExactGMPKind cfg fieldKind = "mpq_set"
       exactSet kind       = error $ "SBV->C: Expected an exact tuple field, received " ++ show kind

       exactClear KUnbounded = "mpz_clear"
       exactClear fieldKind
         | isExactGMPKind cfg fieldKind = "mpq_clear"
       exactClear kind       = error $ "SBV->C: Expected an exact tuple field, received " ++ show kind

-- | Return the helper name that initializes caller-owned storage for an exact
-- tuple.
tupleOwnedInitName :: Kind -> String
tupleOwnedInitName kind = "sbv_tuple_owned_init_" ++ kindTag kind

-- | Return the helper name that assigns into initialized owned tuple storage.
tupleOwnedSetName :: Kind -> String
tupleOwnedSetName kind = "sbv_tuple_owned_set_" ++ kindTag kind

-- | Return the public helper name that deep-copies an exact-field tuple.
tupleOwnedCloneName :: Kind -> String
tupleOwnedCloneName kind = "sbv_tuple_owned_clone_" ++ kindTag kind

-- | Return the public helper name that releases an owned exact-field tuple.
tupleOwnedReleaseName :: Kind -> String
tupleOwnedReleaseName kind = "sbv_tuple_owned_release_" ++ kindTag kind

-- | Initialize a generated-driver tuple and populate its fields from a seed.
-- Exact fields use the public owned-tuple storage protocol; other fields use
-- the supplied scalar renderer.
tupleDriverInit :: CgConfig -> (Kind -> Integer -> Doc) -> Kind -> String -> Integer -> Doc
tupleDriverInit cfg renderValue kind@(KTuple fields) externalName seed =
     text (tupleCType kind) <+> text externalName P.<> semi
  $$ text (tupleOwnedInitName kind) P.<> parens (text "&" P.<> text externalName) P.<> semi
  $$ vcat (concat (zipWith assignField [1 :: Int ..] (zip fields [seed ..])))
 where assignField index (fieldKind, fieldSeed) = assignAt fieldKind access fieldSeed
        where access = text externalName P.<> text "." P.<> text (tupleFieldName index)

       assignAt fieldKind access fieldSeed
         | isExactGMPKind cfg fieldKind
         = exactAssignments fieldKind access fieldSeed
         | nested@(KTuple nestedFields) <- fieldKind
         , tupleUsesExact cfg nested
         = concat (zipWith assignNested [1 :: Int ..] (zip nestedFields [fieldSeed ..]))
         | True
         = [access <+> text "=" <+> renderValue fieldKind fieldSeed P.<> semi]
        where assignNested nestedIndex (nestedKind, nestedSeed) = assignAt nestedKind
                (access P.<> text "." P.<> text (tupleFieldName nestedIndex))
                nestedSeed

       exactAssignments KUnbounded access value =
         [ text "if" <+> parens (text "mpz_set_str" P.<> parens (fsep (punctuate comma [parens (text "mpz_ptr") <+> access, doubleQuotes (integer value), text "10"])) <+> text "!= 0") <+> text "abort" P.<> parens empty P.<> semi]
       exactAssignments fieldKind access value
         | isExactGMPKind cfg fieldKind =
             [ text "if" <+> parens (text "mpq_set_str" P.<> parens (fsep (punctuate comma [parens (text "mpq_ptr") <+> access, doubleQuotes (integer value), text "10"])) <+> text "!= 0") <+> text "abort" P.<> parens empty P.<> semi
             , text "mpq_canonicalize" P.<> parens (parens (text "mpq_ptr") <+> access) P.<> semi
             ]
       exactAssignments fieldKind _ _ = error $ "SBV->C: Expected an exact tuple field, received " ++ show fieldKind
tupleDriverInit _ _ kind _ _ = error $ "SBV->C: Expected a tuple kind, received " ++ show kind

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
                | isExactGMPKind cfg kind = CFunctionScoped
                | tupleUsesExact cfg kind = CFunctionScoped
                | True                    = CByValue

-- | Test whether a tuple contains an exact GMP-backed integer, real, or
-- rational at any nesting depth under the active code-generation configuration.
tupleUsesExact :: CgConfig -> Kind -> Bool
tupleUsesExact cfg kind@KTuple{} = any (isExactGMPKind cfg) (expandKinds kind)
tupleUsesExact _   _             = False

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
elementCType KRational           = "SRational"
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
kindTag KRational          = "rational"
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
