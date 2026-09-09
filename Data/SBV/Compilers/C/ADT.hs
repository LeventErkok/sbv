-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.ADT
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Non-recursive algebraic-data-type lowering for the SBV-to-C compiler.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.ADT
  ( adtKinds
  , adtCType
  , adtTypeDecls
  , adtOwnershipTypeDecls
  , adtOwnedCloneName
  , adtOwnedReleaseName
  , adtDriverInit
  , adtValue
  , adtConst
  , adtExpr
  , adtUsesExact
  , adtDriverValue
  , adtPrint
  ) where

import Data.Char                       (isAlphaNum, isAscii, ord, toUpper)
import Data.List                       (find, nub, sortOn)
import qualified Data.Set as Set
import qualified Data.Text as T
import Numeric                         (showHex)

import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as P ((<>))

import Data.SBV.Compilers.C.BV         (isWideBV, wideBVEqual)
import Data.SBV.Compilers.C.FP         (arbitraryFPEqual, arbitraryFPObjectEqual, nativeFPObjectEqual)
import Data.SBV.Compilers.C.GMP        (gmpEqual, isExactGMPKind)
import Data.SBV.Compilers.C.Lowering   (CLowering, CStorage(..), expressionLowering)
import Data.SBV.Compilers.C.Tuple      ( elementCType
                                       , kindTag
                                       , tupleFieldName
                                       , tupleOwnedInitName
                                       , tupleOwnedReleaseName
                                       , tupleOwnedSetName
                                       , tupleUsesExact
                                       )
import Data.SBV.Compilers.CodeGen      (CgConfig)
import Data.SBV.Core.Data
import Data.SBV.Core.Kind              (expandKinds, substituteADTVars)
import Data.SBV.Core.Symbolic          (ADTOp(..))

-- | Return the concrete, non-built-in ADT kinds used by a program.
adtKinds :: Set.Set Kind -> [Kind]
adtKinds = sortOn adtDepth . nub . filter isConcreteADT . Set.toAscList

-- | Return the public C structure type used for an ADT kind.
adtCType :: Kind -> String
adtCType kind@(KADT typeName parameters _)
  | isConcreteADT kind = "SBVADT_" ++ encodeIdentifier typeName ++ concatMap parameterTag parameters
  | True               = error $ "SBV->C: Expected a concrete ADT kind, received " ++ show kind
 where parameterTag (_, parameterKind) = "_" ++ show (length tag) ++ "_" ++ tag
         where tag = adtKindTag parameterKind
adtCType kind = error $ "SBV->C: Expected an ADT kind, received " ++ show kind

-- | Emit public tagged-union declarations for all ADT kinds used by a program.
adtTypeDecls :: [Kind] -> Doc
adtTypeDecls []   = empty
adtTypeDecls adts = text . unlines $ "/* Non-recursive algebraic data types. */" : concatMap declaration adts
 where declaration kind =
            [ "#ifndef " ++ adtGuard kind
            , "#define " ++ adtGuard kind
            , "typedef enum {"
            ]
         ++ zipWith (enumEntry kind) [1 :: Int ..] (adtConstructors kind)
         ++ [ "} " ++ adtTagCType kind ++ ";"
            , "typedef struct {"
            , "  " ++ adtTagCType kind ++ " tag;"
            ]
         ++ payloadDeclaration kind
         ++ [ "} " ++ adtCType kind ++ ";"
            , "#endif"
            , ""
            ]
       enumEntry kind index _ = "  " ++ adtTagName kind index ++ " = " ++ show (index - 1)
                             ++ if index == length (adtConstructors kind) then "" else ","

       payloadDeclaration kind
         | null populated = []
         | True           = ["  union {"] ++ concatMap constructorPayload populated ++ ["  } payload;"]
        where populated = [(index, fields) | (index, (_, fields)) <- zip [1 :: Int ..] (adtConstructors kind), not (null fields)]
              constructorPayload (constructorIndex, fields) =
                   ["    struct {"]
                ++ zipWith fieldDeclaration [1 :: Int ..] fields
                ++ ["    } " ++ adtConstructorMember constructorIndex ++ ";"]
              fieldDeclaration fieldIndex fieldKind = "      " ++ adtFieldCType fieldKind ++ " " ++ adtFieldName fieldIndex ++ ";"

-- | Emit public ownership helpers for ADTs containing exact GMP-backed
-- fields. Inputs borrow their field storage. Cloned values own the active
-- constructor's exact fields and must be released with
-- 'adtOwnedReleaseName'.
adtOwnershipTypeDecls :: CgConfig -> [Kind] -> Doc
adtOwnershipTypeDecls cfg adts
  | null owned = empty
  | True       = text . unlines $ concatMap declaration owned
 where owned = filter (adtUsesExact cfg) adts

       declaration kind =
          [ "#ifndef " ++ ownershipGuard
          , "#define " ++ ownershipGuard
          , "/* Owned exact-field helpers for " ++ adtCType kind ++ ". */"
          , "/* Owned values have unique ownership; clone before copying and release every owner. */"
          , initSignature
          , "{"
          , "  if (value == NULL) abort();"
          , "  memset(value, 0, sizeof *value);"
          , "  value->tag = tag;"
          , "  switch (tag) {"
          ]
          ++ concatMap (constructorCase initializeField kind) indexedConstructors
          ++ [ "    default: abort();"
          , "  }"
          , "}"
          , ""
          , releaseSignature
          , "{"
          , "  if (value == NULL) return;"
          , "  switch (value->tag) {"
          ]
          ++ concatMap (constructorCase releaseField kind) indexedConstructors
          ++ [ "    default: abort();"
          , "  }"
          , "  memset(value, 0, sizeof *value);"
          , "}"
          , ""
          , setSignature
          , "{"
          , "  if (target == NULL) abort();"
          , "  if (target->tag != source.tag) {"
          , "    " ++ adtOwnedReleaseName kind ++ "(target);"
          , "    " ++ adtOwnedInitName kind ++ "(target, source.tag);"
          , "  }"
          , "  switch (source.tag) {"
          ]
          ++ concatMap (constructorCase setField kind) indexedConstructors
          ++ [ "    default: abort();"
          , "  }"
          , "}"
          , ""
          , cloneSignature
          , "{"
          , "  " ++ adtCType kind ++ " result;"
          , "  " ++ adtOwnedInitName kind ++ "(&result, source.tag);"
          , "  " ++ adtOwnedSetName kind ++ "(&result, source);"
          , "  return result;"
          , "}"
          , "#endif"
          , ""
         ]
         where ownershipGuard = map toUpper (adtCType kind) ++ "_OWNERSHIP_DEFINED"

               initSignature = "static inline SBV_CGEN_UNUSED void "
                            ++ adtOwnedInitName kind
                            ++ "(" ++ adtCType kind ++ " *value, " ++ adtTagCType kind ++ " tag)"

               releaseSignature = "static inline SBV_CGEN_UNUSED void "
                               ++ adtOwnedReleaseName kind
                               ++ "(" ++ adtCType kind ++ " *value)"

               setSignature = "static inline SBV_CGEN_UNUSED void "
                           ++ adtOwnedSetName kind
                           ++ "(" ++ adtCType kind ++ " *target, " ++ adtCType kind ++ " source)"

               cloneSignature = "static inline SBV_CGEN_UNUSED "
                             ++ adtCType kind ++ " " ++ adtOwnedCloneName kind
                             ++ "(" ++ adtCType kind ++ " source)"

               indexedConstructors = zip [1 :: Int ..] (adtConstructors kind)

       constructorCase renderField kind (constructorIndex, (_, fields)) =
          [ "    case " ++ adtTagName kind constructorIndex ++ ": {" ]
          ++ concat (zipWith (renderField constructorIndex) [1 :: Int ..] fields)
          ++ [ "      break;"
          , "    }"
          ]

       initializeField constructorIndex fieldIndex fieldKind
         | isExactGMPKind cfg fieldKind
         = let access  = ownedField "value->" constructorIndex fieldIndex
               mutable = exactMutableType fieldKind
               local   = "field" ++ show constructorIndex ++ "_" ++ show fieldIndex
           in [ "      " ++ mutable ++ " " ++ local ++ " = (" ++ mutable ++ ") malloc(sizeof(*" ++ local ++ "));"
              , "      if (" ++ local ++ " == NULL) abort();"
              , "      " ++ exactInit fieldKind ++ "(" ++ local ++ ");"
              , "      " ++ access ++ " = " ++ local ++ ";"
              ]
         | tupleUsesExact cfg fieldKind
         = [ "      " ++ tupleOwnedInitName fieldKind
          ++ "(&" ++ ownedField "value->" constructorIndex fieldIndex ++ ");"
           ]
         | isConcreteADT fieldKind
         , adtUsesExact cfg fieldKind
         = [ "      " ++ adtOwnedInitName fieldKind
          ++ "(&" ++ ownedField "value->" constructorIndex fieldIndex
          ++ ", " ++ adtTagName fieldKind 1 ++ ");"
           ]
         | True
         = []

       setField constructorIndex fieldIndex fieldKind
         | isExactGMPKind cfg fieldKind
         = [ "      " ++ exactSet fieldKind
          ++ "((" ++ exactMutableType fieldKind ++ ") " ++ target ++ ", " ++ source ++ ");"
           ]
         | tupleUsesExact cfg fieldKind
         = ["      " ++ tupleOwnedSetName fieldKind ++ "(&" ++ target ++ ", " ++ source ++ ");"]
         | isConcreteADT fieldKind
         , adtUsesExact cfg fieldKind
         = ["      " ++ adtOwnedSetName fieldKind ++ "(&" ++ target ++ ", " ++ source ++ ");"]
         | True
         = ["      " ++ target ++ " = " ++ source ++ ";"]
        where target = ownedField "target->" constructorIndex fieldIndex
              source = ownedField "source."  constructorIndex fieldIndex

       releaseField constructorIndex fieldIndex fieldKind
         | isExactGMPKind cfg fieldKind
         = [ "      if (" ++ access ++ " != NULL) {"
           , "        " ++ exactClear fieldKind ++ "((" ++ exactMutableType fieldKind ++ ") " ++ access ++ ");"
           , "        free((void *) " ++ access ++ ");"
           , "      }"
           ]
         | tupleUsesExact cfg fieldKind
         = ["      " ++ tupleOwnedReleaseName fieldKind ++ "(&" ++ access ++ ");"]
         | isConcreteADT fieldKind && adtUsesExact cfg fieldKind
         = ["      " ++ adtOwnedReleaseName fieldKind ++ "(&" ++ access ++ ");"]
         | True
         = []
        where access = ownedField "value->" constructorIndex fieldIndex

       ownedField root constructorIndex fieldIndex = root
                                                    ++ "payload."
                                                    ++ adtConstructorMember constructorIndex
                                                    ++ "."
                                                    ++ adtFieldName fieldIndex

       exactMutableType KUnbounded = "mpz_ptr"
       exactMutableType KReal      = "mpq_ptr"
       exactMutableType kind       = error $ "SBV->C: Expected an exact ADT field, received " ++ show kind

       exactInit KUnbounded = "mpz_init"
       exactInit KReal      = "mpq_init"
       exactInit kind       = error $ "SBV->C: Expected an exact ADT field, received " ++ show kind

       exactSet KUnbounded = "mpz_set"
       exactSet KReal      = "mpq_set"
       exactSet kind       = error $ "SBV->C: Expected an exact ADT field, received " ++ show kind

       exactClear KUnbounded = "mpz_clear"
       exactClear KReal      = "mpq_clear"
       exactClear kind       = error $ "SBV->C: Expected an exact ADT field, received " ++ show kind

-- | Return the helper name that initializes caller-owned storage for one ADT
-- constructor.
adtOwnedInitName :: Kind -> String
adtOwnedInitName kind = "sbv_adt_owned_init_" ++ adtCType kind

-- | Return the helper name that assigns into initialized owned ADT storage.
adtOwnedSetName :: Kind -> String
adtOwnedSetName kind = "sbv_adt_owned_set_" ++ adtCType kind

-- | Return the public helper name that deep-copies an exact-field ADT.
adtOwnedCloneName :: Kind -> String
adtOwnedCloneName kind = "sbv_adt_owned_clone_" ++ adtCType kind

-- | Return the public helper name that releases an owned exact-field ADT.
adtOwnedReleaseName :: Kind -> String
adtOwnedReleaseName kind = "sbv_adt_owned_release_" ++ adtCType kind

-- | Initialize a generated-driver ADT and populate its active constructor
-- from a seed. Exact fields use the public owned-ADT storage protocol; other
-- fields use the supplied scalar renderer.
adtDriverInit :: CgConfig -> (Kind -> Integer -> Doc) -> Kind -> String -> Integer -> Doc
adtDriverInit cfg renderValue kind externalName seed
  | isConcreteADT kind
  , adtUsesExact cfg kind
  =  text (adtCType kind) <+> text externalName P.<> semi
  $$ initialize kind (text externalName) constructorIndex
  $$ vcat (assignConstructor kind (text externalName) constructorIndex fields seed)
  | True
  = error $ "SBV->C: Expected an exact-field ADT, received " ++ show kind
 where constructors = adtConstructors kind
       constructorIndex = fromInteger (mod seed (fromIntegral (length constructors))) + 1
       fields = snd (constructors !! (constructorIndex - 1))

       initialize fieldKind access index = text (adtOwnedInitName fieldKind)
         P.<> parens (fsep (punctuate comma [text "&" P.<> parens access, text (adtTagName fieldKind index)]))
         P.<> semi

       release fieldKind access = text (adtOwnedReleaseName fieldKind)
         P.<> parens (text "&" P.<> parens access)
         P.<> semi

       assignConstructor _ access index fieldKinds fieldSeed = concat
         (zipWith (assignField access index) [1 :: Int ..] (zip fieldKinds [fieldSeed ..]))

       assignField access constructor fieldIndex (nestedKind, nestedSeed) =
         assignAt nestedKind (adtField access constructor fieldIndex) nestedSeed

       assignAt fieldKind access fieldSeed
         | isExactGMPKind cfg fieldKind
         = exactAssignments fieldKind access fieldSeed
         | KTuple fieldKinds <- fieldKind
         , tupleUsesExact cfg fieldKind
         = concat (zipWith assignTupleField [1 :: Int ..] (zip fieldKinds [fieldSeed ..]))
         | isConcreteADT fieldKind
         , adtUsesExact cfg fieldKind
         = let nestedConstructors = adtConstructors fieldKind
               nestedIndex = fromInteger (mod fieldSeed (fromIntegral (length nestedConstructors))) + 1
               nestedFields = snd (nestedConstructors !! (nestedIndex - 1))
           in release fieldKind access
            : initialize fieldKind access nestedIndex
            : assignConstructor fieldKind access nestedIndex nestedFields fieldSeed
         | True
         = [access <+> text "=" <+> renderValue fieldKind fieldSeed P.<> semi]
        where assignTupleField fieldIndex (nestedKind, nestedSeed) = assignAt nestedKind
                (access P.<> text "." P.<> text (tupleFieldName fieldIndex))
                nestedSeed

       exactAssignments KUnbounded access value =
         [setFromString "mpz_set_str" "mpz_ptr" access value]
       exactAssignments KReal access value =
         [ setFromString "mpq_set_str" "mpq_ptr" access value
         , text "mpq_canonicalize" P.<> parens (parens (text "mpq_ptr") <+> access) P.<> semi
         ]
       exactAssignments fieldKind _ _ = error $ "SBV->C: Expected an exact ADT field, received " ++ show fieldKind

       setFromString functionName pointerType access value =
         text "if"
           <+> parens (text functionName
                 P.<> parens (fsep (punctuate comma [ parens (text pointerType) <+> access
                                                    , doubleQuotes (integer value)
                                                    , text "10"
                                                    ]))
                 <+> text "!= 0")
           <+> text "abort" P.<> parens empty P.<> semi

-- | Render a concrete ADT value as a C99 compound literal.
adtConst :: (CV -> Doc) -> CV -> Maybe Doc
adtConst renderValue cv@(CV kind (CADT (constructorName, fieldValues)))
  | isConcreteADT kind
  , Just (constructorIndex, fieldKinds) <- findConstructor kind constructorName
  , map fst fieldValues == fieldKinds
  = Just $ adtValue kind constructorIndex [renderValue (CV fieldKind fieldValue) | (fieldKind, fieldValue) <- fieldValues]
  | isConcreteADT kind
  = error $ "SBV->C: Malformed ADT constant " ++ show cv
adtConst _ _ = Nothing

-- | Lower ADT construction, tests, accessors, equality, conditionals, and labels.
adtExpr :: CgConfig -> Op -> [SV] -> Kind -> [Doc] -> Maybe CLowering
adtExpr cfg op svs resultKind args
  | not (isConcreteADT resultKind || any (isConcreteADT . kindOf) svs)
  = Nothing
  | LkUp{} <- op
  = Nothing
  | Uninterpreted{} <- op
  = Nothing
  | True
  = case (op, svs, args) of
      (ADTOp (ADTConstructor constructorName kind), fields, renderedFields)
        | kind == resultKind
        , Just (constructorIndex, fieldKinds) <- findConstructor kind (T.unpack constructorName)
        , map kindOf fields == fieldKinds
        -> lower resultKind $ adtValue kind constructorIndex renderedFields
      (ADTOp (ADTTester testerName operationResultKind), [value], [renderedValue])
        | operationResultKind == resultKind
        , Just constructorIndex <- findTester (kindOf value) (T.unpack testerName)
        -> lower resultKind $ adtTag renderedValue <+> text "==" <+> text (adtTagName (kindOf value) constructorIndex)
      (ADTOp (ADTAccessor accessorName operationResultKind), [value], [renderedValue])
        | operationResultKind == resultKind
        , Just (constructorIndex, fieldIndex, fieldKind) <- findAccessor (kindOf value) (T.unpack accessorName)
        , fieldKind == resultKind
        -> lower resultKind $ adtField renderedValue constructorIndex fieldIndex
      (Equal strong, [left, right], [renderedLeft, renderedRight])
        | kindOf left == kindOf right
        -> lower resultKind $ adtEqual cfg strong (kindOf left) renderedLeft renderedRight
      (NotEqual, [left, right], [renderedLeft, renderedRight])
        | kindOf left == kindOf right
        -> lower resultKind $ text "!" P.<> parens (adtEqual cfg False (kindOf left) renderedLeft renderedRight)
      (comparison, [left, right], [renderedLeft, renderedRight])
        | adtIsEnumeration (kindOf left)
        , kindOf left == kindOf right
        , Just comparisonSymbol <- adtComparisonSymbol comparison
        -> lower resultKind $ adtTag renderedLeft <+> text comparisonSymbol <+> adtTag renderedRight
      (Ite, [_condition, left, right], [renderedCondition, renderedLeft, renderedRight])
        | resultKind == kindOf left
        , resultKind == kindOf right
        -> lower resultKind $ renderedCondition <+> text "?" <+> renderedLeft <+> text ":" <+> renderedRight
      (Label label, [_], [renderedValue])
        -> lower resultKind $ renderedValue <+> text "/*" <+> text label <+> text "*/"
      _ -> error $ "SBV->C: ADT lowering does not support " ++ adtOperationName op
                ++ " with argument kinds " ++ show (map kindOf svs)
                ++ " and result kind " ++ show resultKind
                ++ "; constructors " ++ show [constructorName | (constructorName, _) <- adtConstructors (sourceADTKind resultKind svs)]
 where lower kind = Just . expressionLowering storage []
        where storage
                | isConcreteADT kind && adtUsesExact cfg kind = CFunctionScoped
                | isExactGMPKind cfg kind                     = CFunctionScoped
                | True                                        = CByValue

-- | Test whether an ADT contains an exact GMP-backed integer or real field.
adtUsesExact :: CgConfig -> Kind -> Bool
adtUsesExact cfg = any constructorUsesExact . adtConstructors
 where constructorUsesExact (_, fields) = any fieldUsesExact fields
       fieldUsesExact = any (isExactGMPKind cfg) . expandKinds

-- | Construct a deterministic driver value, choosing a constructor from the
-- supplied integer and delegating field values to the caller.
adtDriverValue :: (Kind -> Integer -> Doc) -> Kind -> Integer -> Doc
adtDriverValue renderField kind seed
  | null constructors = error $ "SBV->C: Cannot construct an uninterpreted sort in the C driver: " ++ show kind
  | True              = adtValue kind constructorIndex (zipWith renderField fields [seed ..])
 where constructors = adtConstructors kind
       constructorIndex = fromInteger (mod seed (fromIntegral (length constructors))) + 1
       fields = snd (constructors !! (constructorIndex - 1))

-- | Render C statements that print an ADT value by constructor name and fields.
adtPrint :: (Kind -> Doc -> Doc) -> Kind -> Doc -> Doc
adtPrint printField kind value
  = text "switch" <+> parens (adtTag value) <+> text "{"
 $$ nest 2 (vcat (zipWith printConstructor [1 :: Int ..] (adtConstructors kind))
         $$ text "default: printf(\"<invalid ADT tag>\"); break;")
 $$ text "}"
 where printConstructor constructorIndex (constructorName, fields)
         =  text "case" <+> text (adtTagName kind constructorIndex) P.<> colon
         $$ nest 2 (text "printf" P.<> parens (fsep (punctuate comma [text "\"%s\"", text (show constructorName)])) P.<> semi
                 $$ printFields constructorIndex fields
                 $$ text "break" P.<> semi)

       printFields _                []     = empty
       printFields constructorIndex fields =
            text "printf(\"(\");"
         $$ vcat (zipWith (printOne constructorIndex) [1 :: Int ..] fields)
         $$ text "printf(\")\");"

       printOne constructorIndex fieldIndex fieldKind
         =  (if fieldIndex == 1 then empty else text "printf(\", \");")
         $$ printField fieldKind (adtField value constructorIndex fieldIndex)

-- | Return the constructors with all parameter variables replaced by their
-- concrete kinds, rejecting recursive type applications in this first slice.
adtConstructors :: Kind -> [(String, [Kind])]
adtConstructors kind@(KADT typeName parameters constructors)
  | isConcreteADT kind = map substituteConstructor constructors
  | True               = error $ "SBV->C: Expected a concrete ADT kind, received " ++ show kind
 where substituteConstructor (constructorName, fields) = (constructorName, map substituteField fields)
       substituteField field = validateField (substituteADTVars typeName parameters field)
       validateField KApp{} = error $ "SBV->C: Recursive KApp fields are not yet supported in ADT " ++ show kind
       validateField field  = field
adtConstructors kind = error $ "SBV->C: Expected an ADT kind, received " ++ show kind

-- | Render the field-level equality semantics used inside an ADT comparison.
adtFieldEqual :: CgConfig -> Bool -> Kind -> Doc -> Doc -> Doc
adtFieldEqual cfg strong kind left right
  | isWideBV kind                              = wideBVEqual kind left right
  | isFP kind && strong                        = arbitraryFPObjectEqual kind left right
  | isFP kind                                  = arbitraryFPEqual kind left right
  | strong && (isFloat kind || isDouble kind) = nativeFPObjectEqual left right
  | isExactGMPKind cfg kind                    = gmpEqual kind left right
  | KTuple fields <- kind                      = tupleEqual cfg strong fields left right
  | isConcreteADT kind                         = adtEqual cfg strong kind left right
  | True                                       = left <+> text "==" <+> right

-- | Render structural equality for a tuple nested in an ADT field.
tupleEqual :: CgConfig -> Bool -> [Kind] -> Doc -> Doc -> Doc
tupleEqual cfg strong fields left right = andExpressions comparisons
 where comparisons = zipWith compareField [1 :: Int ..] fields
       compareField index fieldKind = adtFieldEqual cfg strong fieldKind
         (parens left  P.<> text ".field" P.<> int index)
         (parens right P.<> text ".field" P.<> int index)

-- | Render tag-sensitive structural equality for two ADT values.
adtEqual :: CgConfig -> Bool -> Kind -> Doc -> Doc -> Doc
adtEqual cfg strong kind left right = parens $ tagEquality <+> text "&&" <+> constructorEquality
 where tagEquality = parens (adtTag left <+> text "==" <+> adtTag right)
       constructorEquality = parens . orExpressions $ zipWith constructorCase [1 :: Int ..] (adtConstructors kind)
       constructorCase constructorIndex (_, fields) = andExpressions
         (parens (adtTag left <+> text "==" <+> text (adtTagName kind constructorIndex))
        : zipWith (fieldEquality constructorIndex) [1 :: Int ..] fields)
       fieldEquality constructorIndex fieldIndex fieldKind = adtFieldEqual cfg strong fieldKind
         (adtField left  constructorIndex fieldIndex)
         (adtField right constructorIndex fieldIndex)

-- | Join Boolean C expressions with short-circuiting conjunction.
andExpressions :: [Doc] -> Doc
andExpressions []          = text "true"
andExpressions expressions = parens (fsep (punctuate (text " &&") expressions))

-- | Join Boolean C expressions with short-circuiting disjunction.
orExpressions :: [Doc] -> Doc
orExpressions []          = text "false"
orExpressions expressions = parens (fsep (punctuate (text " ||") expressions))

-- | Locate a constructor and return its one-based tag and concrete fields.
findConstructor :: Kind -> String -> Maybe (Int, [Kind])
findConstructor kind constructorName = do
  (index, (_, fields)) <- find ((== constructorName) . fst . snd) (zip [1 :: Int ..] (adtConstructors kind))
  pure (index, fields)

-- | Locate the constructor named by a canonical @is-Constructor@ tester.
findTester :: Kind -> String -> Maybe Int
findTester kind testerName = fst <$> find matches (zip [1 :: Int ..] (adtConstructors kind))
 where matches (_, (constructorName, _)) = testerName == "is-" ++ constructorName

-- | Locate the constructor field named by a canonical
-- @getConstructor_fieldIndex@ accessor.
findAccessor :: Kind -> String -> Maybe (Int, Int, Kind)
findAccessor kind accessorName = findMatch candidates
 where candidates = [(constructorIndex, fieldIndex, fieldKind)
                    | (constructorIndex, (constructorName, fields)) <- zip [1 :: Int ..] (adtConstructors kind)
                    , (fieldIndex, fieldKind) <- zip [1 :: Int ..] fields
                    , accessorName == "get" ++ constructorName ++ "_" ++ show fieldIndex
                    ]
       findMatch []    = Nothing
       findMatch (x:_) = Just x

-- | Return the C type used for a supported ADT field.
adtFieldCType :: Kind -> String
adtFieldCType kind@KADT{}
  | isConcreteADT kind = adtCType kind
adtFieldCType kind = elementCType kind

-- | Return whether a kind is a user ADT rather than rounding mode or an
-- uninterpreted sort.
isConcreteADT :: Kind -> Bool
isConcreteADT kind = isADT kind && not (isRoundingMode kind) && not (isUninterpreted kind)

-- | Return the nesting depth used to order dependent ADT declarations.
adtDepth :: Kind -> Int
adtDepth kind
  | isConcreteADT kind = 1 + maximum (0 : map adtDepth (concatMap snd (adtConstructors kind)))
  | KTuple fields <- kind = maximum (0 : map adtDepth fields)
  | True                  = 0

-- | Return a collision-free kind tag for an applied ADT parameter.
adtKindTag :: Kind -> String
adtKindTag kind@KADT{} = "adt_" ++ encodeIdentifier (adtCType kind)
adtKindTag kind        = kindTag kind

-- | Render the tag-selection expression for an ADT value.
adtTag :: Doc -> Doc
adtTag value = parens value P.<> text ".tag"

-- | Render the payload-selection expression for an ADT field.
adtField :: Doc -> Int -> Int -> Doc
adtField value constructorIndex fieldIndex = parens value
  P.<> text ".payload."
  P.<> text (adtConstructorMember constructorIndex)
  P.<> text "."
  P.<> text (adtFieldName fieldIndex)

-- | Return the generated payload member for a one-based constructor index.
adtConstructorMember :: Int -> String
adtConstructorMember index = "constructor" ++ show index

-- | Return the generated field member for a one-based field index.
adtFieldName :: Int -> String
adtFieldName index = "field" ++ show index

-- | Return the generated enumeration type used for an ADT tag.
adtTagCType :: Kind -> String
adtTagCType kind = adtCType kind ++ "_Tag"

-- | Return the generated enumeration constant for one ADT constructor.
adtTagName :: Kind -> Int -> String
adtTagName kind constructorIndex = map toUpper (adtCType kind) ++ "_TAG_" ++ show constructorIndex

-- | Return the preprocessor guard protecting one ADT declaration.
adtGuard :: Kind -> String
adtGuard kind = map toUpper (adtCType kind) ++ "_DEFINED"

-- | Render a C99 tagged-union compound literal.
adtValue :: Kind -> Int -> [Doc] -> Doc
adtValue kind constructorIndex fields
  | constructorIndex < 1 || constructorIndex > length constructors
  = error $ "SBV->C: Invalid ADT constructor index " ++ show constructorIndex ++ " for " ++ show kind
  | length fields /= length expectedFields
  = error $ "SBV->C: ADT literal field mismatch for " ++ show kind
  | True
  = parens (text (adtCType kind)) P.<> braces (fsep (punctuate comma initializers))
 where constructors = adtConstructors kind
       expectedFields = snd (constructors !! (constructorIndex - 1))
       initializers = text ".tag" <+> text "=" <+> text (adtTagName kind constructorIndex)
                    : zipWith initializer [1 :: Int ..] fields
       initializer fieldIndex field = text ".payload."
                                      P.<> text (adtConstructorMember constructorIndex)
                                      P.<> text "."
                                      P.<> text (adtFieldName fieldIndex)
                                      <+> text "=" <+> field

-- | Encode an arbitrary Haskell type name as a valid C identifier component.
encodeIdentifier :: String -> String
encodeIdentifier = concatMap encode
 where encode character
         | isAscii character && isAlphaNum character = [character]
         | True                                      = "_x" ++ showHex (ord character) "" ++ "_"

-- | Return a total diagnostic name for an operation involving an ADT.
adtOperationName :: Op -> String
adtOperationName (ADTOp (ADTConstructor opName _)) = "constructor " ++ show opName
adtOperationName (ADTOp (ADTTester      opName _)) = "tester "      ++ show opName
adtOperationName (ADTOp (ADTAccessor    opName _)) = "accessor "    ++ show opName
adtOperationName LkUp{}                            = "table lookup"
adtOperationName (Equal strong)                    = if strong then "strong equality" else "equality"
adtOperationName NotEqual                          = "inequality"
adtOperationName Ite                               = "conditional"
adtOperationName (Label label)                     = "label " ++ show label
adtOperationName _                                 = "an unsupported operation"

-- | Recover the ADT kind participating in a failed lowering for diagnostics.
sourceADTKind :: Kind -> [SV] -> Kind
sourceADTKind resultKind _
  | isConcreteADT resultKind = resultKind
sourceADTKind _ svs = case filter (isConcreteADT . kindOf) svs of
  value : _ -> kindOf value
  []        -> error "SBV->C: Missing ADT kind in ADT lowering diagnostic"

-- | Return whether every constructor of an ADT is nullary.
adtIsEnumeration :: Kind -> Bool
adtIsEnumeration = all (null . snd) . adtConstructors

-- | Return the C comparison token supported for enumeration ADTs.
adtComparisonSymbol :: Op -> Maybe String
adtComparisonSymbol LessThan    = Just "<"
adtComparisonSymbol GreaterThan = Just ">"
adtComparisonSymbol LessEq      = Just "<="
adtComparisonSymbol GreaterEq   = Just ">="
adtComparisonSymbol _           = Nothing
