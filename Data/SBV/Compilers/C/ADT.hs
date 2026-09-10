-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.ADT
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Algebraic-data-type lowering for the SBV-to-C compiler.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.ADT
  ( adtKinds
  , resolveADTReferences
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
  , adtNeedsOwnership
  , adtDriverValue
  , adtPrint
  , adtPrintHelpers
  ) where

import Data.Char                       (isAlphaNum, isAscii, ord, toUpper)
import qualified Data.Graph as DG
import Data.List                       (find, nub)
import qualified Data.Set as Set
import qualified Data.Text as T
import Numeric                         (showHex)

import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as P ((<>))

import Data.SBV.Compilers.C.BV         (isWideBV, wideBVEqual)
import Data.SBV.Compilers.C.FP         (arbitraryFPEqual, arbitraryFPObjectEqual, nativeFPObjectEqual)
import Data.SBV.Compilers.C.GMP        (isExactGMPKind)
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

-- | A concrete ADT field and whether its declaration is a recursive pointer
-- edge within the same strongly connected component.
data ADTField = ADTField Kind Bool

-- | Return the used concrete, non-built-in ADT kinds in dependency order.
-- The first set supplies every registered ADT template and the second supplies
-- the kinds actually reached by the program. References through 'KApp' are
-- accepted for both acyclic and recursive declarations. Recursive components
-- are kept adjacent so their C layouts can use forward-declared pointer edges.
adtKinds :: Set.Set Kind -> Set.Set Kind -> [Kind]
adtKinds registeredKinds usedKinds = concatMap orderedComponent (DG.stronglyConnComp dependencyNodes)
 where registeredADTs = nub (filter isConcreteADT (Set.toAscList registeredKinds))
       usedADTs       = nub (filter isConcreteADT (Set.toAscList usedKinds))
       adts           = closeRegistry usedADTs

       dependencyNodes = [(kind, adtKey kind, dependencies kind) | kind <- adts]

       closeRegistry current
         | length expanded == length current = current
         | True                              = closeRegistry expanded
        where referenced = [ application
                           | kind <- current
                           , application@KApp{} <- referenceApplications kind
                           ]
              expanded = nub (current ++ map (resolveADTReferences registeredADTs) referenced)

       referenceApplications (KADT typeName parameters constructors) =
         [ application
         | (_, fields) <- constructors
         , field <- fields
         , application@KApp{} <- expandKinds (substituteADTVars typeName parameters field)
         ]
       referenceApplications kind = error $ "SBV->C: Expected an ADT kind, received " ++ show kind

       dependencies kind =
         [ (referencedName, referencedArguments)
         | KApp referencedName referencedArguments <- referenceApplications kind
         ]

       orderedComponent (DG.AcyclicSCC kind)           = [kind]
       orderedComponent (DG.CyclicSCC recursiveKinds) = recursiveKinds

       adtKey (KADT typeName parameters _) = (typeName, map snd parameters)
       adtKey kind = error $ "SBV->C: Expected an ADT kind, received " ++ show kind

-- | Return the public C structure type used for an ADT kind.
adtCType :: Kind -> String
adtCType kind@(KADT typeName parameters _)
  | isConcreteADT kind = "SBVADT_" ++ encodeIdentifier typeName ++ concatMap parameterTag parameters
  | True               = error $ "SBV->C: Expected a concrete ADT kind, received " ++ show kind
 where parameterTag (_, parameterKind) = "_" ++ show (length tag) ++ "_" ++ tag
         where tag = adtKindTag parameterKind
adtCType kind = error $ "SBV->C: Expected an ADT kind, received " ++ show kind

-- | Emit public tagged-union declarations for all ADT kinds used by a program.
adtTypeDecls :: CgConfig -> [Kind] -> Doc
adtTypeDecls _   []   = empty
adtTypeDecls cfg adts = text . unlines $
     [ "/* Algebraic data types. Recursive fields form finite, acyclic pointer graphs. */"
     , "/* Inputs borrow these graphs; owned outputs and returns must be released. */"
     , "#ifndef SBV_CGEN_UNUSED"
     , "#if defined(__GNUC__) || defined(__clang__)"
     , "#define SBV_CGEN_UNUSED __attribute__((unused))"
     , "#else"
     , "#define SBV_CGEN_UNUSED"
     , "#endif"
     , "#endif"
     , ""
     ]
  ++ concatMap forwardDeclaration adts
  ++ concatMap declaration adts
  ++ dereferenceDeclarations
  ++ equalityDeclarations
 where forwardDeclaration kind =
          [ "#ifndef " ++ adtForwardGuard kind
          , "#define " ++ adtForwardGuard kind
          , "typedef struct " ++ adtCType kind ++ " " ++ adtCType kind ++ ";"
          , "#endif"
          , ""
          ]

       declaration kind =
            [ "#ifndef " ++ adtGuard kind
            , "#define " ++ adtGuard kind
            , "typedef enum {"
            ]
         ++ zipWith (enumEntry kind) [1 :: Int ..] constructors
         ++ [ "} " ++ adtTagCType kind ++ ";"
            , "struct " ++ adtCType kind ++ " {"
            , "  " ++ adtTagCType kind ++ " tag;"
            ]
         ++ payloadDeclaration kind
         ++ [ "};"
            , "#endif"
            , ""
            ]
        where constructors = adtConstructorFields adts kind

       enumEntry kind index _ = "  " ++ adtTagName kind index ++ " = " ++ show (index - 1)
                             ++ if index == length (adtConstructorFields adts kind) then "" else ","

       payloadDeclaration kind
         | null populated = []
         | True           = ["  union {"] ++ concatMap constructorPayload populated ++ ["  } payload;"]
        where populated = [ (index, fields)
                          | (index, (_, fields)) <- zip [1 :: Int ..] (adtConstructorFields adts kind)
                          , not (null fields)
                          ]
              constructorPayload (constructorIndex, fields) =
                   ["    struct {"]
                ++ zipWith fieldDeclaration [1 :: Int ..] fields
                ++ ["    } " ++ adtConstructorMember constructorIndex ++ ";"]
              fieldDeclaration fieldIndex field = "      " ++ adtFieldCType field ++ " " ++ adtFieldName fieldIndex ++ ";"

       recursiveKinds = filter (adtIsRecursive adts) adts

       dereferenceDeclarations = concatMap dereferenceDeclaration recursiveKinds

       dereferenceDeclaration kind =
         [ "#ifndef " ++ dereferenceGuard kind
         , "#define " ++ dereferenceGuard kind
         , "static inline SBV_CGEN_UNUSED " ++ adtCType kind ++ " " ++ adtDereferenceName kind
        ++ "(const " ++ adtCType kind ++ " *value)"
         , "{"
         , "  if (value == NULL) abort();"
         , "  return *value;"
         , "}"
         , "#endif"
         , ""
         ]

       equalityDeclarations
         | null recursiveKinds = []
         | True                = concatMap equalityPrototypes [False, True]
                              ++ concatMap equalityDefinitions [False, True]

       equalityPrototypes strong =
         [ "static inline SBV_CGEN_UNUSED bool " ++ adtEqualName strong kind
        ++ "(" ++ adtCType kind ++ " left, " ++ adtCType kind ++ " right);"
         | kind <- recursiveKinds
         ] ++ [""]

       equalityDefinitions strong = concatMap (equalityDefinition strong) recursiveKinds

       equalityDefinition strong kind =
          [ "#ifndef " ++ equalityGuard strong kind
          , "#define " ++ equalityGuard strong kind
          , "static inline SBV_CGEN_UNUSED bool " ++ adtEqualName strong kind
         ++ "(" ++ adtCType kind ++ " left, " ++ adtCType kind ++ " right)"
          , "{"
          , "  if (left.tag != right.tag) return false;"
          , "  switch (left.tag) {"
          ]
        ++ concatMap (equalityCase strong kind) (zip [1 :: Int ..] (adtConstructorFields adts kind))
        ++ [ "    default: abort();"
           , "  }"
           , "}"
           , "#endif"
           , ""
           ]

       equalityCase strong kind (constructorIndex, (_, fields)) =
          ["    case " ++ adtTagName kind constructorIndex ++ ":"]
        ++ concatMap (nullChecks constructorIndex) (zip [1 :: Int ..] fields)
        ++ ["      return " ++ render (andExpressions comparisons) ++ ";"]
        where comparisons = zipWith (compareField strong kind constructorIndex) [1 :: Int ..] fields

       nullChecks constructorIndex (fieldIndex, ADTField _ True) =
         [ "      if (" ++ render (adtField (text "left") constructorIndex fieldIndex) ++ " == NULL"
        ++ " || " ++ render (adtField (text "right") constructorIndex fieldIndex) ++ " == NULL) abort();"
         ]
       nullChecks _ _ = []

       compareField strong _ constructorIndex fieldIndex (ADTField fieldKind recursive)
         | recursive = text (adtEqualName strong fieldKind)
                    P.<> parens (fsep (punctuate comma [deref "left", deref "right"]))
         | True      = adtFieldEqual cfg adts strong fieldKind
                         (adtField (text "left")  constructorIndex fieldIndex)
                         (adtField (text "right") constructorIndex fieldIndex)
        where deref side = text "*" P.<> parens (adtField (text side) constructorIndex fieldIndex)

-- | Emit public ownership helpers for ADTs containing exact GMP-backed fields
-- or recursive pointers. Inputs borrow their field storage. Cloned values own
-- the active constructor's managed fields and must be released with
-- 'adtOwnedReleaseName'.
adtOwnershipTypeDecls :: CgConfig -> [Kind] -> Doc
adtOwnershipTypeDecls cfg adts
  | null owned = empty
  | True       = text . unlines $ concatMap prototypes owned ++ concatMap declaration owned
 where owned = filter (adtNeedsOwnership cfg adts) adts

       prototypes kind =
         [ "static inline SBV_CGEN_UNUSED void " ++ adtOwnedInitName kind
        ++ "(" ++ adtCType kind ++ " *value, " ++ adtTagCType kind ++ " tag);"
         , "static inline SBV_CGEN_UNUSED void " ++ adtOwnedReleaseName kind
        ++ "(" ++ adtCType kind ++ " *value);"
         , "static inline SBV_CGEN_UNUSED void " ++ adtOwnedSetName kind
        ++ "(" ++ adtCType kind ++ " *target, " ++ adtCType kind ++ " source);"
         , "static inline SBV_CGEN_UNUSED " ++ adtCType kind ++ " " ++ adtOwnedCloneName kind
        ++ "(" ++ adtCType kind ++ " source);"
         , ""
         ]

       declaration kind =
          [ "#ifndef " ++ ownershipGuard
          , "#define " ++ ownershipGuard
          , "/* Deep-ownership helpers for " ++ adtCType kind ++ ". */"
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

               indexedConstructors = zip [1 :: Int ..] (adtConstructorFields adts kind)

       constructorCase renderField kind (constructorIndex, (_, fields)) =
          [ "    case " ++ adtTagName kind constructorIndex ++ ": {" ]
          ++ concat (zipWith (renderField constructorIndex) [1 :: Int ..] fields)
          ++ [ "      break;"
          , "    }"
          ]

       initializeField constructorIndex fieldIndex (ADTField fieldKind recursive)
         | recursive
         = []
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
         , adtNeedsOwnership cfg adts fieldKind
         = [ "      " ++ adtOwnedInitName fieldKind
          ++ "(&" ++ ownedField "value->" constructorIndex fieldIndex
          ++ ", " ++ adtTagName fieldKind 1 ++ ");"
           ]
         | True
         = []

       setField constructorIndex fieldIndex (ADTField fieldKind recursive)
         | recursive
         = [ "      " ++ adtCType fieldKind ++ " *" ++ copy
          ++ " = (" ++ adtCType fieldKind ++ " *) malloc(sizeof *" ++ copy ++ ");"
           , "      if (" ++ copy ++ " == NULL || " ++ source ++ " == NULL) abort();"
           , "      *" ++ copy ++ " = " ++ adtOwnedCloneName fieldKind ++ "(*" ++ source ++ ");"
           , "      if (" ++ target ++ " != NULL) {"
           , "        " ++ adtOwnedReleaseName fieldKind ++ "(" ++ target ++ ");"
           , "        free(" ++ target ++ ");"
           , "      }"
           , "      " ++ target ++ " = " ++ copy ++ ";"
           ]
         | isExactGMPKind cfg fieldKind
         = [ "      " ++ exactSet fieldKind
          ++ "((" ++ exactMutableType fieldKind ++ ") " ++ target ++ ", " ++ source ++ ");"
           ]
         | tupleUsesExact cfg fieldKind
         = ["      " ++ tupleOwnedSetName fieldKind ++ "(&" ++ target ++ ", " ++ source ++ ");"]
         | isConcreteADT fieldKind
         , adtNeedsOwnership cfg adts fieldKind
         = ["      " ++ adtOwnedSetName fieldKind ++ "(&" ++ target ++ ", " ++ source ++ ");"]
         | True
         = ["      " ++ target ++ " = " ++ source ++ ";"]
        where target = ownedField "target->" constructorIndex fieldIndex
              source = ownedField "source."  constructorIndex fieldIndex
              copy   = "copy" ++ show constructorIndex ++ "_" ++ show fieldIndex

       releaseField constructorIndex fieldIndex (ADTField fieldKind recursive)
         | recursive
         = [ "      if (" ++ access ++ " != NULL) {"
           , "        " ++ adtOwnedReleaseName fieldKind ++ "(" ++ access ++ ");"
           , "        free(" ++ access ++ ");"
           , "      }"
           ]
         | isExactGMPKind cfg fieldKind
         = [ "      if (" ++ access ++ " != NULL) {"
           , "        " ++ exactClear fieldKind ++ "((" ++ exactMutableType fieldKind ++ ") " ++ access ++ ");"
           , "        free((void *) " ++ access ++ ");"
           , "      }"
           ]
         | tupleUsesExact cfg fieldKind
         = ["      " ++ tupleOwnedReleaseName fieldKind ++ "(&" ++ access ++ ");"]
         | isConcreteADT fieldKind && adtNeedsOwnership cfg adts fieldKind
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

-- | Return the public helper name that deep-copies an owned ADT.
adtOwnedCloneName :: Kind -> String
adtOwnedCloneName kind = "sbv_adt_owned_clone_" ++ adtCType kind

-- | Return the public helper name that releases an owned ADT.
adtOwnedReleaseName :: Kind -> String
adtOwnedReleaseName kind = "sbv_adt_owned_release_" ++ adtCType kind

-- | Initialize a generated-driver ADT and populate its active constructor
-- from a seed. Managed fields use the public owned-ADT storage protocol; other
-- fields use the supplied scalar renderer.
adtDriverInit :: CgConfig -> [Kind] -> (Kind -> Integer -> Doc) -> Kind -> String -> Integer -> Doc
adtDriverInit cfg adts renderValue kind externalName seed
  | isConcreteADT kind
  , adtNeedsOwnership cfg adts kind
  =  text (adtCType kind) <+> text externalName P.<> semi
  $$ initialize kind (text externalName) constructorIndex
  $$ vcat (assignConstructor maximumDepth kind (text externalName) constructorIndex fields seed)
  | True
  = error $ "SBV->C: Expected an owned ADT, received " ++ show kind
 where maximumDepth = max 3 (length adts + 1)
       (constructorIndex, fields) = chooseConstructor maximumDepth kind seed

       initialize fieldKind access index = text (adtOwnedInitName fieldKind)
         P.<> parens (fsep (punctuate comma [text "&" P.<> parens access, text (adtTagName fieldKind index)]))
         P.<> semi

       release fieldKind access = text (adtOwnedReleaseName fieldKind)
         P.<> parens (text "&" P.<> parens access)
         P.<> semi

       assignConstructor depth _ access index fieldKinds fieldSeed = concat
         (zipWith (assignField depth access index) [1 :: Int ..] (zip fieldKinds [fieldSeed ..]))

       assignField depth access constructor fieldIndex (field, nestedSeed) =
         assignAt depth field (adtField access constructor fieldIndex) nestedSeed

       assignAt depth (ADTField fieldKind recursive) access fieldSeed
         | recursive
         = let nestedDepth                   = depth - 1
               (nestedIndex, nestedFields)  = chooseConstructor nestedDepth fieldKind fieldSeed
               dereferenced                 = text "*" P.<> parens access
           in [ access <+> text "=" <+> parens (text (adtCType fieldKind) <+> text "*")
                  <+> text "malloc" P.<> parens (text "sizeof" <+> text "*" P.<> parens access) P.<> semi
              , text "if" <+> parens (access <+> text "== NULL") <+> text "abort" P.<> parens empty P.<> semi
              , initialize fieldKind dereferenced nestedIndex
              ]
           ++ assignConstructor nestedDepth fieldKind dereferenced nestedIndex nestedFields fieldSeed
         | isExactGMPKind cfg fieldKind
         = exactAssignments fieldKind access fieldSeed
         | KTuple fieldKinds <- fieldKind
         , tupleUsesExact cfg fieldKind
         = concat (zipWith assignTupleField [1 :: Int ..] (zip fieldKinds [fieldSeed ..]))
         | isConcreteADT fieldKind
         , adtNeedsOwnership cfg adts fieldKind
         = let (nestedIndex, nestedFields) = chooseConstructor depth fieldKind fieldSeed
           in release fieldKind access
            : initialize fieldKind access nestedIndex
            : assignConstructor depth fieldKind access nestedIndex nestedFields fieldSeed
         | True
         = [access <+> text "=" <+> renderValue fieldKind fieldSeed P.<> semi]
        where assignTupleField fieldIndex (nestedKind, nestedSeed) = assignAt depth (ADTField nestedKind False)
                (access P.<> text "." P.<> text (tupleFieldName fieldIndex))
                nestedSeed

       chooseConstructor depth fieldKind fieldSeed
         | null eligible = error $ "SBV->C: Recursive ADT " ++ show fieldKind
                                ++ " has no finite constructor for a generated driver value"
         | True          = let (index, (_, selectedFields)) = eligible !! fromInteger (mod fieldSeed (fromIntegral (length eligible)))
                           in (index, selectedFields)
        where eligible = [(index, constructor)
                         | (index, constructor@(_, candidateFields)) <- zip [1 :: Int ..] (adtConstructorFields adts fieldKind)
                         , all (fits depth) candidateFields
                         ]

       fits _     (ADTField _         False) = True
       fits depth (ADTField fieldKind True)  = depth > 0 && constructible (depth - 1) fieldKind

       constructible depth fieldKind = any (all (fits depth) . snd) (adtConstructorFields adts fieldKind)

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
  , Just (constructorIndex, fieldKinds) <- findConstructor localADTs kind constructorName
  , map fst fieldValues == fieldKinds
  = Just $ adtValue localADTs kind constructorIndex
        [renderValue (CV fieldKind fieldValue) | (fieldKind, fieldValue) <- fieldValues]
  | isConcreteADT kind
  = error $ "SBV->C: Malformed ADT constant " ++ show cv
 where localKinds = Set.fromList $ kind : concatMap (expandKinds . fst) fieldValues
       localADTs  = adtKinds localKinds localKinds
adtConst _ _ = Nothing

-- | Lower ADT construction, tests, accessors, equality, conditionals, and labels.
adtExpr :: CgConfig -> [Kind] -> Op -> [SV] -> Kind -> [Doc] -> Maybe CLowering
adtExpr cfg adts op svs resultKind args
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
        , Just (constructorIndex, fieldKinds) <- findConstructor adts kind (T.unpack constructorName)
        , map kindOf fields == fieldKinds
        -> lower resultKind $ adtValue adts kind constructorIndex renderedFields
      (ADTOp (ADTTester testerName operationResultKind), [value], [renderedValue])
        | operationResultKind == resultKind
        , Just constructorIndex <- findTester adts (kindOf value) (T.unpack testerName)
        -> lower resultKind $ adtTag renderedValue <+> text "==" <+> text (adtTagName (kindOf value) constructorIndex)
      (ADTOp (ADTAccessor accessorName operationResultKind), [value], [renderedValue])
        | operationResultKind == resultKind
        , Just (constructorIndex, fieldIndex, fieldKind, recursive) <- findAccessor adts (kindOf value) (T.unpack accessorName)
        , fieldKind == resultKind
        -> lower resultKind $ if recursive
                              then text (adtDereferenceName fieldKind)
                                P.<> parens (adtField renderedValue constructorIndex fieldIndex)
                              else adtField renderedValue constructorIndex fieldIndex
      (Equal strong, [left, right], [renderedLeft, renderedRight])
        | kindOf left == kindOf right
        -> lower resultKind $ adtEqual cfg adts strong (kindOf left) renderedLeft renderedRight
      (NotEqual, [left, right], [renderedLeft, renderedRight])
        | kindOf left == kindOf right
        -> lower resultKind $ text "!" P.<> parens (adtEqual cfg adts False (kindOf left) renderedLeft renderedRight)
      (comparison, [left, right], [renderedLeft, renderedRight])
        | adtIsEnumeration adts (kindOf left)
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
                ++ "; constructors "
                ++ show [constructorName | (constructorName, _) <- adtConstructors adts (sourceADTKind resultKind svs)]
 where lower kind = Just . expressionLowering storage []
        where storage
                | isConcreteADT kind && adtNeedsOwnership cfg adts kind = CFunctionScoped
                | isExactGMPKind cfg kind                               = CFunctionScoped
                | True                                                  = CByValue

-- | Test whether an ADT contains an exact GMP-backed integer or real field.
adtUsesExact :: CgConfig -> [Kind] -> Kind -> Bool
adtUsesExact cfg adts = any constructorUsesExact . adtConstructors adts
 where constructorUsesExact (_, fields) = any fieldUsesExact fields
       fieldUsesExact = any (isExactGMPKind cfg) . expandKinds

-- | Test whether an ADT needs deep ownership because it contains exact storage,
-- recursive pointers, or another ADT with either property.
adtNeedsOwnership :: CgConfig -> [Kind] -> Kind -> Bool
adtNeedsOwnership cfg adts = needsOwnership Set.empty
 where needsOwnership visited kind
         | kind `Set.member` visited = adtIsRecursive adts kind
         | adtUsesExact cfg adts kind = True
         | True                       = any (any fieldNeedsOwnership . snd) (adtConstructorFields adts kind)
        where next = Set.insert kind visited
              fieldNeedsOwnership (ADTField _         True)  = True
              fieldNeedsOwnership (ADTField fieldKind False)
                | isConcreteADT fieldKind        = needsOwnership next fieldKind
                | KTuple fieldKinds <- fieldKind = any compositeNeedsOwnership fieldKinds
                | True                           = False
              compositeNeedsOwnership nestedKind
                | isConcreteADT nestedKind        = needsOwnership next nestedKind
                | KTuple nestedKinds <- nestedKind = any compositeNeedsOwnership nestedKinds
                | True                            = False

-- | Construct a deterministic driver value, choosing a constructor from the
-- supplied integer and delegating field values to the caller.
adtDriverValue :: [Kind] -> (Kind -> Integer -> Doc) -> Kind -> Integer -> Doc
adtDriverValue adts renderField = construct (max 3 (length adts + 1))
 where construct :: Int -> Kind -> Integer -> Doc
       construct depth kind seed
         | null constructors = error $ "SBV->C: Cannot construct an uninterpreted sort in the C driver: " ++ show kind
         | True              = adtValue adts kind constructorIndex (zipWith renderADTField fields [seed ..])
        where constructors     = adtConstructorFields adts kind
              eligible = [ (index, constructor)
                         | (index, constructor@(_, candidateFields)) <- zip [1 :: Int ..] constructors
                         , all (fits depth) candidateFields
                         ]
              (constructorIndex, (_, fields))
                | null eligible = error $ "SBV->C: Recursive ADT " ++ show kind
                                       ++ " has no finite constructor for a generated driver value"
                | True          = eligible !! fromInteger (mod seed (fromIntegral (length eligible)))

              renderADTField (ADTField fieldKind recursive) fieldSeed
                | isConcreteADT fieldKind = construct (if recursive then depth - 1 else depth) fieldKind fieldSeed
                | True                    = renderField fieldKind fieldSeed

       fits _     (ADTField _         False) = True
       fits depth (ADTField fieldKind True)  = depth > 0 && constructible (depth - 1) fieldKind

       constructible depth kind = any (all (fits depth) . snd) (adtConstructorFields adts kind)

-- | Render C statements that print an ADT value by constructor name and fields.
adtPrint :: [Kind] -> (Kind -> Doc -> Doc) -> Kind -> Doc -> Doc
adtPrint adts printField kind value
  | adtIsRecursive adts kind = text (adtPrintName kind) P.<> parens value P.<> semi
  | True                     = adtPrintSwitch adts printField kind value

-- | Emit mutually recursive driver-side printers for recursive ADTs.
adtPrintHelpers :: [Kind] -> (Kind -> Doc -> Doc) -> Doc
adtPrintHelpers adts printField
  | null recursiveKinds = empty
  | True                = vcat (map prototype recursiveKinds)
                       $$ text ""
                       $$ vcat (map definition recursiveKinds)
 where recursiveKinds = filter (adtIsRecursive adts) adts
       prototype kind = text "static void" <+> text (adtPrintName kind)
                     P.<> parens (text (adtCType kind) <+> text "value")
                     P.<> semi
       definition kind = text "#ifndef" <+> text (adtPrintGuard kind)
                      $$ text "#define" <+> text (adtPrintGuard kind)
                      $$ text "static void" <+> text (adtPrintName kind)
                      P.<> parens (text (adtCType kind) <+> text "value")
                      $$ text "{"
                      $$ nest 2 (adtPrintSwitch adts printField kind (text "value"))
                      $$ text "}"
                      $$ text "#endif"
                      $$ text ""

-- | Render the tag switch shared by inline and recursive ADT printers.
adtPrintSwitch :: [Kind] -> (Kind -> Doc -> Doc) -> Kind -> Doc -> Doc
adtPrintSwitch adts printField kind value
  = text "switch" <+> parens (adtTag value) <+> text "{"
 $$ nest 2 (vcat (zipWith printConstructor [1 :: Int ..] (adtConstructorFields adts kind))
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

       printOne constructorIndex fieldIndex (ADTField fieldKind recursive)
         =  (if fieldIndex == 1 then empty else text "printf(\", \");")
         $$ if recursive
            then text "if" <+> parens (fieldValue <+> text "== NULL")
              <+> text "printf(\"<null recursive ADT>\");"
              <+> text "else"
              <+> printField fieldKind (text "*" P.<> parens fieldValue)
            else printField fieldKind fieldValue
        where fieldValue = adtField value constructorIndex fieldIndex

-- | Return the driver-side printer name for a recursive ADT.
adtPrintName :: Kind -> String
adtPrintName kind = "sbv_adt_print_" ++ adtCType kind

-- | Return the preprocessor guard for one driver-side recursive ADT printer.
adtPrintGuard :: Kind -> String
adtPrintGuard kind = map toUpper (adtPrintName kind) ++ "_DEFINED"

-- | Return constructors with parameter variables and 'KApp' references
-- replaced by their concrete kinds.
adtConstructors :: [Kind] -> Kind -> [(String, [Kind])]
adtConstructors adts kind = [(constructorName, [fieldKind | ADTField fieldKind _ <- fields])
                            | (constructorName, fields) <- adtConstructorFields adts kind
                            ]

-- | Return concrete constructor fields while retaining which direct 'KApp'
-- references must use pointers to break recursive C layouts.
adtConstructorFields :: [Kind] -> Kind -> [(String, [ADTField])]
adtConstructorFields adts kind@(KADT typeName parameters constructors)
  | isConcreteADT kind = map substituteConstructor constructors
  | True               = error $ "SBV->C: Expected a concrete ADT kind, received " ++ show kind
 where substituteConstructor (constructorName, fields) = (constructorName, map substituteField fields)

       substituteField field = ADTField concrete recursive
        where substituted = substituteADTVars typeName parameters field
              concrete    = resolveADTReferences adts substituted
              recursive   = case substituted of
                              KApp{} -> adtReachable adts concrete kind
                              _      -> False
adtConstructorFields _ kind = error $ "SBV->C: Expected an ADT kind, received " ++ show kind

-- | Return whether the second ADT is reachable from the first through ADT
-- declaration references. The visited set makes recursive registries finite.
adtReachable :: [Kind] -> Kind -> Kind -> Bool
adtReachable adts source target = walk Set.empty source
 where walk visited current
         | current == target            = True
         | current `Set.member` visited = False
         | True                         = any (walk (Set.insert current visited)) (adtDependencies adts current)

-- | Return the concrete ADTs referenced directly or through composite fields
-- by one concrete ADT declaration.
adtDependencies :: [Kind] -> Kind -> [Kind]
adtDependencies adts (KADT typeName parameters constructors) = nub
  [ resolveADTReferences adts application
  | (_, fields) <- constructors
  , field <- fields
  , application@KApp{} <- expandKinds (substituteADTVars typeName parameters field)
  ]
adtDependencies _ kind = error $ "SBV->C: Expected an ADT kind, received " ++ show kind

-- | Resolve concrete ADT applications occurring inside a supported composite
-- field without recursively expanding the referenced declaration.
resolveADTReferences :: [Kind] -> Kind -> Kind
resolveADTReferences adts kind@(KApp typeName arguments) =
  case [ (parameters, constructors)
       | KADT candidateName parameters constructors <- adts
       , candidateName == typeName
       , length parameters == length arguments
       ] of
    ((parameters, constructors) : _) -> KADT typeName (zip (map fst parameters) arguments) constructors
    [] -> error $ "SBV->C: Cannot resolve ADT reference " ++ show kind
             ++ "; available concrete ADTs: " ++ show adts
resolveADTReferences adts (KList elementKind) = KList (resolveADTReferences adts elementKind)
resolveADTReferences adts (KSet elementKind) = KSet (resolveADTReferences adts elementKind)
resolveADTReferences adts (KTuple fieldKinds) = KTuple (map (resolveADTReferences adts) fieldKinds)
resolveADTReferences adts (KArray keyKind valueKind) =
  KArray (resolveADTReferences adts keyKind) (resolveADTReferences adts valueKind)
resolveADTReferences _ kind = kind

-- | Render the field-level equality semantics used inside an ADT comparison.
adtFieldEqual :: CgConfig -> [Kind] -> Bool -> Kind -> Doc -> Doc -> Doc
adtFieldEqual cfg adts strong kind left right
  | isWideBV kind                              = wideBVEqual kind left right
  | isFP kind && strong                        = arbitraryFPObjectEqual kind left right
  | isFP kind                                  = arbitraryFPEqual kind left right
  | strong && (isFloat kind || isDouble kind) = nativeFPObjectEqual left right
  | isExactGMPKind cfg kind                    = adtExactEqual kind left right
  | KTuple fields <- kind                      = tupleEqual cfg adts strong fields left right
  | isConcreteADT kind                         = adtEqual cfg adts strong kind left right
  | True                                       = left <+> text "==" <+> right

-- | Render exact equality directly with GMP's public comparison API so
-- recursive helpers remain self-contained in generated headers.
adtExactEqual :: Kind -> Doc -> Doc -> Doc
adtExactEqual KUnbounded left right = text "mpz_cmp"
                                   P.<> parens (fsep (punctuate comma [left, right]))
                                   <+> text "== 0"
adtExactEqual KReal left right = text "mpq_cmp"
                              P.<> parens (fsep (punctuate comma [left, right]))
                              <+> text "== 0"
adtExactEqual kind _ _ = error $ "SBV->C: Expected an exact ADT field, received " ++ show kind

-- | Render structural equality for a tuple nested in an ADT field.
tupleEqual :: CgConfig -> [Kind] -> Bool -> [Kind] -> Doc -> Doc -> Doc
tupleEqual cfg adts strong fields left right = andExpressions comparisons
 where comparisons = zipWith compareField [1 :: Int ..] fields
       compareField index fieldKind = adtFieldEqual cfg adts strong fieldKind
         (parens left  P.<> text ".field" P.<> int index)
         (parens right P.<> text ".field" P.<> int index)

-- | Render tag-sensitive structural equality for two ADT values.
adtEqual :: CgConfig -> [Kind] -> Bool -> Kind -> Doc -> Doc -> Doc
adtEqual cfg adts strong kind left right
  | adtIsRecursive adts kind = text (adtEqualName strong kind)
                            P.<> parens (fsep (punctuate comma [left, right]))
  | True                     = parens $ tagEquality <+> text "&&" <+> constructorEquality
 where tagEquality = parens (adtTag left <+> text "==" <+> adtTag right)
       constructorEquality = parens . orExpressions $ zipWith constructorCase [1 :: Int ..] (adtConstructors adts kind)
       constructorCase constructorIndex (_, fields) = andExpressions
         (parens (adtTag left <+> text "==" <+> text (adtTagName kind constructorIndex))
        : zipWith (fieldEquality constructorIndex) [1 :: Int ..] fields)
       fieldEquality constructorIndex fieldIndex fieldKind = adtFieldEqual cfg adts strong fieldKind
         (adtField left  constructorIndex fieldIndex)
         (adtField right constructorIndex fieldIndex)

-- | Return whether an ADT has at least one pointer-backed recursive field.
adtIsRecursive :: [Kind] -> Kind -> Bool
adtIsRecursive adts = any (any recursive . snd) . adtConstructorFields adts
 where recursive (ADTField _ isRecursive) = isRecursive

-- | Return the generated structural-equality helper for a recursive ADT.
adtEqualName :: Bool -> Kind -> String
adtEqualName strong kind = "sbv_adt_" ++ (if strong then "object_" else "")
                        ++ "equal_" ++ adtCType kind

-- | Return the guard protecting one recursive ADT equality-helper definition.
equalityGuard :: Bool -> Kind -> String
equalityGuard strong kind = map toUpper (adtEqualName strong kind) ++ "_DEFINED"

-- | Return the generated checked-dereference helper for a recursive ADT edge.
adtDereferenceName :: Kind -> String
adtDereferenceName kind = "sbv_adt_dereference_" ++ adtCType kind

-- | Return the guard protecting one recursive ADT dereference helper.
dereferenceGuard :: Kind -> String
dereferenceGuard kind = map toUpper (adtDereferenceName kind) ++ "_DEFINED"

-- | Join Boolean C expressions with short-circuiting conjunction.
andExpressions :: [Doc] -> Doc
andExpressions []          = text "true"
andExpressions expressions = parens (fsep (punctuate (text " &&") expressions))

-- | Join Boolean C expressions with short-circuiting disjunction.
orExpressions :: [Doc] -> Doc
orExpressions []          = text "false"
orExpressions expressions = parens (fsep (punctuate (text " ||") expressions))

-- | Locate a constructor and return its one-based tag and concrete fields.
findConstructor :: [Kind] -> Kind -> String -> Maybe (Int, [Kind])
findConstructor adts kind constructorName = do
  (index, (_, fields)) <- find ((== constructorName) . fst . snd)
                               (zip [1 :: Int ..] (adtConstructors adts kind))
  pure (index, fields)

-- | Locate the constructor named by a canonical @is-Constructor@ tester.
findTester :: [Kind] -> Kind -> String -> Maybe Int
findTester adts kind testerName = fst <$> find matches (zip [1 :: Int ..] (adtConstructors adts kind))
 where matches (_, (constructorName, _)) = testerName == "is-" ++ constructorName

-- | Locate the constructor field named by a canonical
-- @getConstructor_fieldIndex@ accessor.
findAccessor :: [Kind] -> Kind -> String -> Maybe (Int, Int, Kind, Bool)
findAccessor adts kind accessorName = findMatch candidates
 where candidates = [(constructorIndex, fieldIndex, fieldKind, recursive)
                    | (constructorIndex, (constructorName, fields)) <- zip [1 :: Int ..] (adtConstructorFields adts kind)
                    , (fieldIndex, ADTField fieldKind recursive) <- zip [1 :: Int ..] fields
                    , accessorName == "get" ++ constructorName ++ "_" ++ show fieldIndex
                    ]
       findMatch []    = Nothing
       findMatch (x:_) = Just x

-- | Return the C type used for a supported ADT field, introducing a pointer
-- precisely for a recursive dependency edge.
adtFieldCType :: ADTField -> String
adtFieldCType (ADTField kind True) = adtCType kind ++ " *"
adtFieldCType (ADTField kind False)
  | isConcreteADT kind = adtCType kind
adtFieldCType (ADTField kind False) = elementCType kind

-- | Return whether a kind is a user ADT rather than rounding mode or an
-- uninterpreted sort.
isConcreteADT :: Kind -> Bool
isConcreteADT kind = isADT kind && not (isRoundingMode kind) && not (isUninterpreted kind)

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

-- | Return the preprocessor guard protecting one ADT forward declaration.
adtForwardGuard :: Kind -> String
adtForwardGuard kind = map toUpper (adtCType kind) ++ "_DECLARED"

-- | Render a C99 tagged-union compound literal.
adtValue :: [Kind] -> Kind -> Int -> [Doc] -> Doc
adtValue adts kind constructorIndex fields
  | constructorIndex < 1 || constructorIndex > length constructors
  = error $ "SBV->C: Invalid ADT constructor index " ++ show constructorIndex ++ " for " ++ show kind
  | length fields /= length expectedFields
  = error $ "SBV->C: ADT literal field mismatch for " ++ show kind
  | True
  = parens (text (adtCType kind)) P.<> braces (fsep (punctuate comma initializers))
 where constructors = adtConstructors adts kind
       expectedFields = snd (constructors !! (constructorIndex - 1))
       initializers = text ".tag" <+> text "=" <+> text (adtTagName kind constructorIndex)
                    : zipWith initializer [1 :: Int ..] (zip fields fieldInfo)
       fieldInfo = snd (adtConstructorFields adts kind !! (constructorIndex - 1))
       initializer fieldIndex (field, ADTField fieldKind recursive) = text ".payload."
                                                                    P.<> text (adtConstructorMember constructorIndex)
                                                                    P.<> text "."
                                                                    P.<> text (adtFieldName fieldIndex)
                                                                    <+> text "=" <+> storedField
        where storedField
                | recursive = text "&" P.<> parens (parens (text (adtCType fieldKind) P.<> brackets (text "1"))
                                              P.<> braces field)
                                      P.<> brackets (text "0")
                | True      = field

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
adtIsEnumeration :: [Kind] -> Kind -> Bool
adtIsEnumeration adts = all (null . snd) . adtConstructors adts

-- | Return the C comparison token supported for enumeration ADTs.
adtComparisonSymbol :: Op -> Maybe String
adtComparisonSymbol LessThan    = Just "<"
adtComparisonSymbol GreaterThan = Just ">"
adtComparisonSymbol LessEq      = Just "<="
adtComparisonSymbol GreaterEq   = Just ">="
adtComparisonSymbol _           = Nothing
