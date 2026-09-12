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
  , adtForwardTypeDecls
  , adtTypeDecls
  , adtTypeDeclsFor
  , adtDeclarationDependencies
  , adtEqualityRuntimeDecls
  , adtEqualityRuntime
  , adtOwnershipTypePrototypes
  , adtOwnershipTypeDecls
  , adtOwnedCloneName
  , adtOwnedReleaseName
  , adtDriverInit
  , adtCollectionDriverInit
  , collectionUsesADT
  , adtValue
  , adtConst
  , adtExpr
  , adtUsesExact
  , adtNeedsOwnership
  , adtIsRecursive
  , adtDriverValue
  , adtPrint
  , adtPrintHelpers
  , adtConstructors
  ) where

import qualified Data.Graph as DG
import Data.List                       (find, nub)
import qualified Data.Set as Set
import qualified Data.Text as T

import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as P ((<>))

import Data.SBV.Compilers.C.Array      (arrayStoredLoad, arrayStoredValue)
import Data.SBV.Compilers.C.BV         (isWideBV, wideBVEqual)
import Data.SBV.Compilers.C.FP         (arbitraryFPEqual, arbitraryFPObjectEqual, nativeFPObjectEqual)
import Data.SBV.Compilers.C.GMP        (isExactGMPKind)
import Data.SBV.Compilers.C.List       ( listClone
                                       , listDriverClear
                                       , listDriverInit
                                       , listEqual
                                       , listNeedsDriverInit
                                       , listRelease
                                       )
import Data.SBV.Compilers.C.Lowering   (CLowering(..), CStorage(..), expressionLowering)
import Data.SBV.Compilers.C.Set        ( setClone
                                       , setDriverClear
                                       , setDriverInit
                                       , setEqual
                                       , setNeedsDriverInit
                                       , setRelease
                                       )
import Data.SBV.Compilers.C.Tuple      ( tupleOwnedInitName
                                       , tupleOwnedReleaseName
                                       , tupleOwnedSetName
                                       , tupleNeedsOwnership
                                       )
import Data.SBV.Compilers.C.Types      (adtCType, elementCType, tupleFieldName)
import Data.SBV.Compilers.C.Value      (byValueEqual, managedValueClone, managedValueRelease, valueNeedsOwnership)
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

-- | Emit forward declarations that permit collection descriptors to refer to
-- ADT element types before their tagged-union layouts are complete.
adtForwardTypeDecls :: [Kind] -> Doc
adtForwardTypeDecls []   = empty
adtForwardTypeDecls adts = text . unlines $ concatMap forwardDeclaration adts
 where forwardDeclaration kind =
         [ "#ifndef " ++ adtForwardGuard kind
         , "#define " ++ adtForwardGuard kind
         , "typedef struct " ++ adtCType kind ++ " " ++ adtCType kind ++ ";"
         , "#endif"
         , ""
         ]

-- | Emit public tagged-union declarations for all ADT kinds used by a program.
adtTypeDecls :: CgConfig -> [Kind] -> Doc
adtTypeDecls cfg adts = adtTypeDeclsFor cfg adts adts

-- | Emit selected public tagged-union declarations using the complete ADT
-- registry to resolve constructor fields. This supports dependency-ordered
-- interleaving with tuple declarations.
adtTypeDeclsFor :: CgConfig -> [Kind] -> [Kind] -> Doc
adtTypeDeclsFor _ _        []           = empty
adtTypeDeclsFor _ registry declarations = text . unlines $
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
  ++ concatMap forwardDeclaration declarations
  ++ concatMap declaration declarations
  ++ dereferenceDeclarations
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
        where constructors = adtConstructorFields registry kind

       enumEntry kind index _ = "  " ++ adtTagName kind index ++ " = " ++ show (index - 1)
                             ++ if index == length (adtConstructorFields registry kind) then "" else ","

       payloadDeclaration kind
         | null populated = []
         | True           = ["  union {"] ++ concatMap constructorPayload populated ++ ["  } payload;"]
        where populated = [ (index, fields)
                          | (index, (_, fields)) <- zip [1 :: Int ..] (adtConstructorFields registry kind)
                          , not (null fields)
                          ]
              constructorPayload (constructorIndex, fields) =
                   ["    struct {"]
                ++ zipWith fieldDeclaration [1 :: Int ..] fields
                ++ ["    } " ++ adtConstructorMember constructorIndex ++ ";"]
              fieldDeclaration fieldIndex field = "      " ++ adtFieldCType field ++ " " ++ adtFieldName fieldIndex ++ ";"

       recursiveKinds = filter (adtIsRecursive registry) declarations

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

-- | Return complete by-value tuple and ADT dependencies of one ADT layout.
-- Recursive pointer fields need only a forward declaration and are excluded.
adtDeclarationDependencies :: [Kind] -> Kind -> [Kind]
adtDeclarationDependencies adts kind = nub
  [ fieldKind
  | (_, fields) <- adtConstructorFields adts kind
  , ADTField fieldKind recursive <- fields
  , not recursive
  , isTuple fieldKind || isConcreteADT fieldKind
  ]

-- | Emit forward declarations for the ADT equality helpers used by collection
-- element comparisons.
adtEqualityRuntimeDecls :: [Kind] -> Doc
adtEqualityRuntimeDecls []   = empty
adtEqualityRuntimeDecls adts = text . unlines $ concatMap prototypes [False, True]
 where prototypes strong =
         [ "static SBV_CGEN_UNUSED bool " ++ adtEqualName strong kind
        ++ "(" ++ adtCType kind ++ " left, " ++ adtCType kind ++ " right);"
         | kind <- adts
         ] ++ [""]

-- | Emit private structural-equality helpers for concrete ADTs. These
-- definitions follow the collection runtimes so managed fields can reuse the
-- same list and set equality semantics as top-level expressions.
adtEqualityRuntime :: CgConfig -> [Kind] -> Doc
adtEqualityRuntime cfg adts
  | null adts = empty
  | True      = text . unlines $ concatMap definitions [False, True]
 where definitions strong = concatMap (definition strong) adts

       definition strong kind =
          [ "static SBV_CGEN_UNUSED bool " ++ adtEqualName strong kind
         ++ "(" ++ adtCType kind ++ " left, " ++ adtCType kind ++ " right)"
          , "{"
          , "  if (left.tag != right.tag) return false;"
          , "  switch (left.tag) {"
          ]
        ++ concatMap (equalityCase strong kind) (zip [1 :: Int ..] (adtConstructorFields adts kind))
        ++ [ "    default: abort();"
           , "  }"
           , "}"
           , ""
           ]

       equalityCase strong kind (constructorIndex, (_, fields)) =
          ["    case " ++ adtTagName kind constructorIndex ++ ":"]
        ++ concatMap (nullChecks constructorIndex) (zip [1 :: Int ..] fields)
        ++ ["      return " ++ render (andExpressions comparisons) ++ ";"]
        where comparisons = zipWith (compareField strong constructorIndex) [1 :: Int ..] fields

       nullChecks constructorIndex (fieldIndex, ADTField _ True) =
         [ "      if (" ++ render (adtField (text "left") constructorIndex fieldIndex) ++ " == NULL"
        ++ " || " ++ render (adtField (text "right") constructorIndex fieldIndex) ++ " == NULL) abort();"
         ]
       nullChecks _ _ = []

       compareField strong constructorIndex fieldIndex (ADTField fieldKind recursive)
         | recursive = text (adtEqualName strong fieldKind)
                    P.<> parens (fsep (punctuate comma [deref "left", deref "right"]))
         | True      = adtFieldEqual cfg adts strong fieldKind
                         (adtField (text "left")  constructorIndex fieldIndex)
                         (adtField (text "right") constructorIndex fieldIndex)
        where deref side = text "*" P.<> parens (adtField (text side) constructorIndex fieldIndex)

-- | Emit forward declarations for the uniform ADT ownership helpers. These
-- precede tuple helper definitions so tuples and ADTs can contain one another
-- without imposing an ownership-definition order.
adtOwnershipTypePrototypes :: [Kind] -> Doc
adtOwnershipTypePrototypes []   = empty
adtOwnershipTypePrototypes adts = text . unlines $ concatMap prototypes adts
 where prototypes kind =
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

-- | Emit public ownership-helper definitions for concrete ADTs. Inputs borrow
-- their field storage. Cloned values own all managed fields of the active
-- constructor and must be released with 'adtOwnedReleaseName'; by-value ADTs
-- use the same uniform protocol so collections need no representation-specific
-- branch.
adtOwnershipTypeDecls :: CgConfig -> [Kind] -> Doc
adtOwnershipTypeDecls cfg adts
  | null adts = empty
  | True      = text . unlines $ concatMap declaration adts
 where declaration kind =
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
         where ownershipGuard = adtCType kind ++ "_OWNERSHIP_DEFINED"

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
         | fieldKind == KString
         = [ "      " ++ ownedField "value->" constructorIndex fieldIndex
          ++ " = (SString) {NULL, 0, 0};"
           ]
         | isList fieldKind
         = [ "      " ++ ownedField "value->" constructorIndex fieldIndex
          ++ " = (" ++ elementCType fieldKind ++ ") {NULL, 0};"
           ]
         | isSet fieldKind
         = [ "      " ++ ownedField "value->" constructorIndex fieldIndex
          ++ " = (" ++ elementCType fieldKind ++ ") {NULL, 0, false};"
           ]
         | isArray fieldKind
         = ["      " ++ ownedField "value->" constructorIndex fieldIndex ++ " = NULL;"]
         | tupleNeedsOwnership cfg fieldKind
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
         | fieldKind == KString
         = [ "      const SString " ++ copy
          ++ " = " ++ render (managedValueClone fieldKind (text source)) ++ ";"
           , "      " ++ render (managedValueRelease fieldKind (text ("&" ++ target)))
           , "      " ++ target ++ " = " ++ copy ++ ";"
           ]
         | isList fieldKind
         = [ "      const " ++ elementCType fieldKind ++ " " ++ copy
          ++ " = " ++ render (listClone fieldKind (text source)) ++ ";"
           , "      " ++ render (listRelease fieldKind (text target))
           , "      " ++ target ++ " = " ++ copy ++ ";"
           ]
         | isSet fieldKind
         = [ "      const " ++ elementCType fieldKind ++ " " ++ copy
          ++ " = " ++ render (setClone fieldKind (text source)) ++ ";"
           , "      " ++ render (setRelease fieldKind (text target))
           , "      " ++ target ++ " = " ++ copy ++ ";"
           ]
         | isArray fieldKind
         = [ "      " ++ elementCType fieldKind ++ " " ++ copy
          ++ " = " ++ render (managedValueClone fieldKind (text source)) ++ ";"
           , "      " ++ render (managedValueRelease fieldKind (text ("&" ++ target)))
           , "      " ++ target ++ " = " ++ copy ++ ";"
           ]
         | tupleNeedsOwnership cfg fieldKind
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
         | fieldKind == KString
         = ["      " ++ render (managedValueRelease fieldKind (text ("&" ++ access)))]
         | isList fieldKind
         = ["      " ++ render (listRelease fieldKind (text access))]
         | isSet fieldKind
         = ["      " ++ render (setRelease fieldKind (text access))]
         | isArray fieldKind
         = ["      " ++ render (managedValueRelease fieldKind (text ("&" ++ access)))]
         | tupleNeedsOwnership cfg fieldKind
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
       exactMutableType fieldKind
         | isExactGMPKind cfg fieldKind = "mpq_ptr"
       exactMutableType kind       = error $ "SBV->C: Expected an exact ADT field, received " ++ show kind

       exactInit KUnbounded = "mpz_init"
       exactInit fieldKind
         | isExactGMPKind cfg fieldKind = "mpq_init"
       exactInit kind       = error $ "SBV->C: Expected an exact ADT field, received " ++ show kind

       exactSet KUnbounded = "mpz_set"
       exactSet fieldKind
         | isExactGMPKind cfg fieldKind = "mpq_set"
       exactSet kind       = error $ "SBV->C: Expected an exact ADT field, received " ++ show kind

       exactClear KUnbounded = "mpz_clear"
       exactClear fieldKind
         | isExactGMPKind cfg fieldKind = "mpq_clear"
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
-- fields use the supplied scalar renderer. The statement renderer initializes
-- retained values that occur through nested aggregate fields.
adtDriverInit :: CgConfig -> [Kind] -> (Kind -> Integer -> Doc) -> (Kind -> String -> Integer -> Doc) -> Kind -> String -> Integer -> Doc
adtDriverInit cfg adts renderValue initializeValue kind externalName seed
  | isConcreteADT kind
  , adtNeedsOwnership cfg adts kind
  =  text (adtCType kind) <+> text externalName P.<> semi
  $$ initialize kind (text externalName) constructorIndex
  $$ vcat (assignConstructor maximumDepth kind (text externalName) externalName constructorIndex fields seed)
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

       assignConstructor depth _ access accessName index fieldKinds fieldSeed = concat
         (zipWith (assignField depth access accessName index) [1 :: Int ..] (zip fieldKinds [fieldSeed ..]))

       assignField depth access accessName constructor fieldIndex (field, nestedSeed) =
         assignAt depth field fieldAccess fieldName nestedSeed
        where fieldAccess = adtField access constructor fieldIndex
              fieldName   = accessName ++ "_constructor_" ++ show constructor ++ "_field_" ++ show fieldIndex

       assignAt depth (ADTField fieldKind recursive) access accessName fieldSeed
         | recursive
         = let nestedDepth                   = depth - 1
               (nestedIndex, nestedFields)  = chooseConstructor nestedDepth fieldKind fieldSeed
               dereferenced                 = text "*" P.<> parens access
           in [ access <+> text "=" <+> parens (text (adtCType fieldKind) <+> text "*")
                  <+> text "malloc" P.<> parens (text "sizeof" <+> text "*" P.<> parens access) P.<> semi
              , text "if" <+> parens (access <+> text "== NULL") <+> text "abort" P.<> parens empty P.<> semi
              , initialize fieldKind dereferenced nestedIndex
              ]
           ++ assignConstructor nestedDepth fieldKind dereferenced (accessName ++ "_recursive") nestedIndex nestedFields fieldSeed
         | isExactGMPKind cfg fieldKind
         = exactAssignments fieldKind access fieldSeed
         | fieldKind == KString
         = [access <+> text "=" <+> managedValueClone fieldKind (renderValue fieldKind fieldSeed) P.<> semi]
         | isArray fieldKind
         = [ initializeValue fieldKind accessName fieldSeed
           , access <+> text "=" <+> text accessName P.<> semi
           ]
         | isList fieldKind
         = collectionAssignment listNeedsDriverInit listDriverInit listDriverClear listClone
         | isSet fieldKind
         = collectionAssignment setNeedsDriverInit setDriverInit setDriverClear setClone
         | KTuple fieldKinds <- fieldKind
         , tupleNeedsOwnership cfg fieldKind
         = concat (zipWith assignTupleField [1 :: Int ..] (zip fieldKinds [fieldSeed ..]))
         | isConcreteADT fieldKind
         , adtNeedsOwnership cfg adts fieldKind
         = let (nestedIndex, nestedFields) = chooseConstructor depth fieldKind fieldSeed
           in release fieldKind access
            : initialize fieldKind access nestedIndex
            : assignConstructor depth fieldKind access accessName nestedIndex nestedFields fieldSeed
         | True
         = [access <+> text "=" <+> renderValue fieldKind fieldSeed P.<> semi]
        where assignTupleField fieldIndex (nestedKind, nestedSeed) = assignAt depth (ADTField nestedKind False) nestedAccess nestedName nestedSeed
                where nestedAccess = access P.<> text "." P.<> text (tupleFieldName fieldIndex)
                      nestedName   = accessName ++ "_field_" ++ show fieldIndex

              collectionAssignment needsDriverInit driverInit driverClear clone
                | needsDriverInit cfg fieldKind
                = [ driverInit cfg renderValue initializeValue fieldKind accessName fieldSeed
                  , access <+> text "=" <+> clone fieldKind (text accessName) P.<> semi
                  , driverClear cfg fieldKind accessName
                  ]
                | True
                = [access <+> text "=" <+> clone fieldKind (renderValue fieldKind fieldSeed) P.<> semi]

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
       exactAssignments fieldKind access value
         | isExactGMPKind cfg fieldKind =
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

-- | Initialize a generated-driver list or set whose direct elements are ADTs.
-- The descriptor borrows the independently initialized element variables.
adtCollectionDriverInit :: CgConfig -> [Kind] -> (Kind -> Integer -> Doc) -> (Kind -> String -> Integer -> Doc) -> Kind -> String -> Integer -> Doc
adtCollectionDriverInit cfg adts renderValue initializeValue kind externalName seed
  | Just elementKind <- collectionADTElement kind
  =  vcat (zipWith (initializeElement elementKind) elementNames [seed ..])
  $$ text "const" <+> text (adtCType elementKind) <+> text dataName P.<> brackets (int elementCount)
       <+> text "=" <+> braces (fsep (punctuate comma (map text elementNames))) P.<> semi
  $$ text "const" <+> text (elementCType kind) <+> text externalName <+> text "="
       <+> braces (fsep (punctuate comma descriptorFields)) P.<> semi
  | True
  = error $ "SBV->C: Expected a collection with direct ADT elements, received " ++ show kind
 where elementCount     = 3
       elementNames     = [externalName ++ "_element_" ++ show index | index <- [0 :: Int .. elementCount - 1]]
       dataName         = externalName ++ "_data"
       descriptorFields = [text dataName, int elementCount]
                       ++ case kind of
                            KSet{} -> [text (if odd seed then "true" else "false")]
                            _      -> []

       initializeElement elementKind elementName elementSeed
         | adtNeedsOwnership cfg adts elementKind
         = adtDriverInit cfg adts renderValue initializeValue elementKind elementName elementSeed
         | True
         = text (adtCType elementKind) <+> text elementName <+> text "="
             <+> adtDriverValue adts renderValue elementKind elementSeed P.<> semi

-- | Test whether a list or set has a concrete ADT as its direct element kind.
collectionUsesADT :: Kind -> Bool
collectionUsesADT kind = case collectionADTElement kind of
                           Just{}  -> True
                           Nothing -> False

-- | Return the concrete direct ADT element of a collection kind.
collectionADTElement :: Kind -> Maybe Kind
collectionADTElement (KList elementKind)
  | isConcreteADT elementKind = Just elementKind
collectionADTElement (KSet elementKind)
  | isConcreteADT elementKind = Just elementKind
collectionADTElement _ = Nothing

-- | Render a concrete ADT value as a C99 compound literal.
adtConst :: (CV -> Doc) -> CV -> Maybe Doc
adtConst renderValue cv@(CV kind (CADT (constructorName, fieldValues)))
  | isConcreteADT kind
  , Just (constructorIndex, fieldKinds) <- findConstructor localADTs kind constructorName
  , map fst fieldValues == fieldKinds
  = Just $ adtValue localADTs kind constructorIndex
        [arrayStoredValue fieldKind (renderValue (CV fieldKind fieldValue)) | (fieldKind, fieldValue) <- fieldValues]
  | isConcreteADT kind
  = error $ "SBV->C: Malformed ADT constant " ++ show cv
 where localKinds = Set.fromList $ kind : concatMap (expandKinds . fst) fieldValues
       localADTs  = adtKinds localKinds localKinds
adtConst _ _ = Nothing

-- | Lower ADT construction, tests, accessors, equality, conditionals, and labels.
adtExpr :: CgConfig -> [Kind] -> Op -> [SV] -> SV -> [Doc] -> Maybe CLowering
adtExpr cfg adts op svs resultSV args
  | not (isConcreteADT resultKind || any (isConcreteADT . kindOf) svs)
  = Nothing
  | LkUp{} <- op
  = Nothing
  | TupleConstructor{} <- op
  = Nothing
  | TupleAccess{} <- op
  = Nothing
  | Uninterpreted{} <- op
  = Nothing
  | True
  = case (op, svs, args) of
      (ADTOp (ADTConstructor constructorName kind), fields, renderedFields)
        | kind == resultKind
        , Just (constructorIndex, fieldKinds) <- findConstructor adts kind (T.unpack constructorName)
        , map kindOf fields == fieldKinds
        -> lowerConstructor kind constructorIndex (zipWith arrayStoredValue fieldKinds renderedFields)
      (ADTOp (ADTTester testerName operationResultKind), [value], [renderedValue])
        | operationResultKind == resultKind
        , Just constructorIndex <- findTester adts (kindOf value) (T.unpack testerName)
        -> lower resultKind $ adtTag renderedValue <+> text "==" <+> text (adtTagName (kindOf value) constructorIndex)
      -- The operation records SBV's scalar result kind, which strips any
      -- surrounding arrays. The accessor field and result SV retain the full kind.
      (ADTOp (ADTAccessor accessorName _operationResultKind), [value], [renderedValue])
        | Just (constructorIndex, fieldIndex, fieldKind, recursive) <- findAccessor adts (kindOf value) (T.unpack accessorName)
        , fieldKind == resultKind
        -> let field = if recursive
                       then text (adtDereferenceName fieldKind)
                         P.<> parens (adtField renderedValue constructorIndex fieldIndex)
                       else adtField renderedValue constructorIndex fieldIndex
           in if isArray resultKind then Just (arrayStoredLoad resultSV field) else lower resultKind field
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
 where resultKind = kindOf resultSV

       lower kind = Just . expressionLowering storage []
        where storage
                | isConcreteADT kind && adtNeedsOwnership cfg adts kind = CFunctionScoped
                | isExactGMPKind cfg kind                               = CFunctionScoped
                | tupleNeedsOwnership cfg kind                          = CFunctionScoped
                | isList kind                                           = CFunctionScoped
                | isSet kind                                            = CFunctionScoped
                | isArray kind                                          = CFunctionScoped
                | True                                                  = CByValue

       lowerConstructor kind constructorIndex renderedFields
         | null recursiveFields
         = lower kind (adtValue adts kind constructorIndex renderedFields)
         | True
         = Just CLowering
             { loweringExpression   = adtValueWithStorage adts kind constructorIndex storeField renderedFields
             , loweringDeclarations = [text (adtCType fieldKind) <+> text (backingName fieldIndex) P.<> semi
                                      | (fieldIndex, fieldKind, _) <- recursiveFields
                                      ]
             , loweringSetup        = [text (backingName fieldIndex) <+> text "=" <+> field P.<> semi
                                      | (fieldIndex, _, field) <- recursiveFields
                                      ]
             , loweringCleanup      = []
             , loweringRequirements = Set.empty
             , loweringStorage      = CFunctionScoped
             }
        where fieldInfo = snd (adtConstructorFields adts kind !! (constructorIndex - 1))
              recursiveFields = [ (fieldIndex, fieldKind, field)
                                | (fieldIndex, (ADTField fieldKind True, field)) <- zip [1 :: Int ..] (zip fieldInfo renderedFields)
                                ]

              backingName fieldIndex = "__sbv_adt_recursive_" ++ show resultSV ++ "_" ++ show fieldIndex

              storeField fieldIndex _ True  _     = text "&" P.<> text (backingName fieldIndex)
              storeField _          _ False field = field

-- | Test whether an ADT contains an exact GMP-backed integer, real, or
-- rational field.
adtUsesExact :: CgConfig -> [Kind] -> Kind -> Bool
adtUsesExact cfg adts = any constructorUsesExact . adtConstructors adts
 where constructorUsesExact (_, fields) = any fieldUsesExact fields
       fieldUsesExact = any (isExactGMPKind cfg) . expandKinds

-- | Test whether an ADT needs deep ownership because it contains collection
-- storage, exact storage, recursive pointers, or another managed aggregate.
adtNeedsOwnership :: CgConfig -> [Kind] -> Kind -> Bool
adtNeedsOwnership cfg adts = needsOwnership Set.empty
 where needsOwnership visited kind
         | kind `Set.member` visited = adtIsRecursive adts kind
         | adtUsesExact cfg adts kind = True
         | True                       = any (any fieldNeedsOwnership . snd) (adtConstructorFields adts kind)
        where next = Set.insert kind visited
              fieldNeedsOwnership (ADTField _         True)  = True
              fieldNeedsOwnership (ADTField fieldKind False)
                | isConcreteADT fieldKind = needsOwnership next fieldKind
                | True                    = valueNeedsOwnership cfg fieldKind

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
       prototype kind = text "static SBV_CGEN_UNUSED void" <+> text (adtPrintName kind)
                     P.<> parens (text (adtCType kind) <+> text "value")
                     P.<> semi
       definition kind = text "#ifndef" <+> text (adtPrintGuard kind)
                      $$ text "#define" <+> text (adtPrintGuard kind)
                      $$ text "static SBV_CGEN_UNUSED void" <+> text (adtPrintName kind)
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
adtPrintGuard kind = adtPrintName kind ++ "_DEFINED"

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
  | kind == KString                            = byValueEqual cfg strong kind left right
  | isList kind                                = listEqual kind left right
  | isSet kind                                 = setEqual kind left right
  | isArray kind                               = byValueEqual cfg strong kind left right
  | KTuple fields <- kind                      = tupleEqual cfg adts strong fields left right
  | isConcreteADT kind                         = adtEqual cfg adts strong kind left right
  | True                                       = left <+> text "==" <+> right

-- | Render exact equality directly with GMP's public comparison API.
adtExactEqual :: Kind -> Doc -> Doc -> Doc
adtExactEqual KUnbounded left right = text "mpz_cmp"
                                   P.<> parens (fsep (punctuate comma [left, right]))
                                   <+> text "== 0"
adtExactEqual exactKind left right
  | exactKind `elem` [KReal, KRational]
  = text "mpq_cmp"
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

-- | Return the generated checked-dereference helper for a recursive ADT edge.
adtDereferenceName :: Kind -> String
adtDereferenceName kind = "sbv_adt_dereference_" ++ adtCType kind

-- | Return the guard protecting one recursive ADT dereference helper.
dereferenceGuard :: Kind -> String
dereferenceGuard kind = adtDereferenceName kind ++ "_DEFINED"

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
adtTagName kind constructorIndex = adtCType kind ++ "_TAG_" ++ show constructorIndex

-- | Return the preprocessor guard protecting one ADT declaration.
adtGuard :: Kind -> String
adtGuard kind = adtCType kind ++ "_DEFINED"

-- | Return the preprocessor guard protecting one ADT forward declaration.
adtForwardGuard :: Kind -> String
adtForwardGuard kind = adtCType kind ++ "_DECLARED"

-- | Render a C99 tagged-union compound literal.
adtValue :: [Kind] -> Kind -> Int -> [Doc] -> Doc
adtValue adts kind constructorIndex = adtValueWithStorage adts kind constructorIndex storeField
 where storeField _ fieldKind True field
         = text "&"
        P.<> parens (   parens (text (adtCType fieldKind) P.<> brackets (text "1"))
                    P.<> braces field
                   )
        P.<> brackets (text "0")
       storeField _ _ False field = field

-- | Render a C99 tagged-union compound literal while allowing the caller to
-- choose how each recursive pointer field receives its backing storage.
adtValueWithStorage :: [Kind] -> Kind -> Int -> (Int -> Kind -> Bool -> Doc -> Doc) -> [Doc] -> Doc
adtValueWithStorage adts kind constructorIndex storeField fields
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
                                                                    <+> text "=" <+> storeField fieldIndex fieldKind recursive field

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
