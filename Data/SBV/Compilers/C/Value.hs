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
  , valueDriverNeedsInitialization
  , byValueEqual
  , managedValueClone
  , managedValueRelease
  , valueDriverInit
  , valueDriverClear
  ) where

import Text.PrettyPrint.HughesPJ
import qualified Text.PrettyPrint.HughesPJ as P ((<>))

import Data.SBV.Compilers.C.BV         (isWideBV, wideBVEqual)
import Data.SBV.Compilers.C.FP         (arbitraryFPEqual, arbitraryFPObjectEqual, nativeFPObjectEqual)
import Data.SBV.Compilers.C.GMP        (gmpDriverClear, gmpDriverInit, gmpEqual, isExactGMPKind)
import Data.SBV.Compilers.C.Types      (adtCType, elementCType, kindTag, tupleCType, tupleFieldName)
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

-- | Test whether a deterministic example-driver value needs declarations or
-- initialization statements instead of a single C compound literal.
valueDriverNeedsInitialization :: CgConfig -> Kind -> Bool
valueDriverNeedsInitialization cfg kind
  | isExactGMPKind cfg kind = True
valueDriverNeedsInitialization cfg (KTuple fields)      = any (valueNeedsOwnership cfg) fields
valueDriverNeedsInitialization cfg (KList elementKind)  = valueDriverNeedsInitialization cfg elementKind
valueDriverNeedsInitialization cfg (KSet elementKind)   = valueDriverNeedsInitialization cfg elementKind
valueDriverNeedsInitialization _   kind@KADT{}          = isConcreteADT kind
valueDriverNeedsInitialization _   _                    = False

-- | Render equality for a scalar or recursively nested aggregate. The Boolean
-- flag selects object equality for floating-point values.
byValueEqual :: CgConfig -> Bool -> Kind -> Doc -> Doc -> Doc
byValueEqual cfg strong kind left right
  | isWideBV kind                              = wideBVEqual kind left right
  | isFP kind && strong                        = arbitraryFPObjectEqual kind left right
  | isFP kind                                  = arbitraryFPEqual kind left right
  | strong && (isFloat kind || isDouble kind) = nativeFPObjectEqual left right
  | isExactGMPKind cfg kind                    = gmpEqual kind left right
  | kind == KString                            = parens $ call "sbv_text_compare" [left, right] <+> text "== 0"
  | KList elementKind <- kind                  = call ("sbv_list_" ++ kindTag elementKind ++ "_equal") [left, right]
  | KSet elementKind <- kind                   = call ("sbv_set_" ++ kindTag elementKind ++ "_equal") [left, right]
  | KTuple fields <- kind                      = tupleEquality fields
  | isConcreteADT kind                         = call (adtEqualityName strong kind) [left, right]
  | True                                       = left <+> text "==" <+> right
 where tupleEquality fields = parens . fsep . punctuate (text " &&") $
         zipWith equalField [1 :: Int ..] fields

       equalField index fieldKind = byValueEqual cfg strong fieldKind
         (parens left  P.<> text "." P.<> text (tupleFieldName index))
         (parens right P.<> text "." P.<> text (tupleFieldName index))

       adtEqualityName objectEquality adtKind
         = "sbv_adt_" ++ (if objectEquality then "object_" else "") ++ "equal_" ++ adtCType adtKind

-- | Deep-copy one non-GMP managed value. Exact GMP values require initialized
-- destination storage and are therefore handled by their aggregate owner.
managedValueClone :: Kind -> Doc -> Doc
managedValueClone KString value             = call "sbv_string_clone" [value]
managedValueClone (KList elementKind) value = call ("sbv_list_clone_" ++ kindTag elementKind) [value]
managedValueClone (KSet elementKind) value  = call ("sbv_set_clone_" ++ kindTag elementKind) [value]
managedValueClone kind@KTuple{} value       = call ("sbv_tuple_owned_clone_" ++ kindTag kind) [value]
managedValueClone kind@KADT{} value
  | isConcreteADT kind                       = call ("sbv_adt_owned_clone_" ++ adtCType kind) [value]
managedValueClone kind _                    = error $ "SBV->C: Expected a non-GMP managed kind, received " ++ show kind

-- | Release one non-GMP managed value through a pointer to its owned storage.
managedValueRelease :: Kind -> Doc -> Doc
managedValueRelease KString address             = call "sbv_string_release" [address] P.<> semi
managedValueRelease (KList elementKind) address = call ("sbv_list_release_" ++ kindTag elementKind) [address] P.<> semi
managedValueRelease (KSet elementKind) address  = call ("sbv_set_release_" ++ kindTag elementKind) [address] P.<> semi
managedValueRelease kind@KTuple{} address       = call ("sbv_tuple_owned_release_" ++ kindTag kind) [address] P.<> semi
managedValueRelease kind@KADT{} address
  | isConcreteADT kind                          = call ("sbv_adt_owned_release_" ++ adtCType kind) [address] P.<> semi
managedValueRelease kind _                      = error $ "SBV->C: Expected a non-GMP managed kind, received " ++ show kind

-- | Declare and initialize one deterministic example-driver value. Managed
-- aggregates receive unique ownership; collection descriptors themselves
-- borrow the element variables declared alongside them.
valueDriverInit :: CgConfig -> (Kind -> Integer -> Doc) -> Kind -> String -> Integer -> Doc
valueDriverInit cfg _           kind                       externalName seed
  | isExactGMPKind cfg kind
  = gmpDriverInit kind (text externalName) (integer seed)
valueDriverInit cfg renderValue kind@(KTuple fields)       externalName seed
  | valueNeedsOwnership cfg kind
  =  text (tupleCType kind) <+> text externalName P.<> semi
  $$ call ("sbv_tuple_owned_init_" ++ kindTag kind) [text "&" P.<> text externalName] P.<> semi
  $$ vcat (concat (zipWith initializeTupleField [1 :: Int ..] (zip fields [seed ..])))
 where initializeTupleField index (fieldKind, fieldSeed) = initializeAt fieldKind access fieldName fieldSeed
        where access    = text externalName P.<> text "." P.<> text (tupleFieldName index)
              fieldName = externalName ++ "_field_" ++ show index

       initializeAt fieldKind access fieldName fieldSeed
         | isExactGMPKind cfg fieldKind = exactAssignment fieldKind access fieldSeed
         | fieldKind == KString         = [access <+> text "=" <+> managedValueClone fieldKind (renderValue fieldKind fieldSeed) P.<> semi]
         | KList{}         <- fieldKind = collectionAssignment fieldKind access fieldName fieldSeed
         | KSet{}          <- fieldKind = collectionAssignment fieldKind access fieldName fieldSeed
         | nested@KTuple{} <- fieldKind
         , valueNeedsOwnership cfg nested
         = concat (zipWith initializeNested [1 :: Int ..] (zip (tupleFields nested) [fieldSeed ..]))
         | True                           = [access <+> text "=" <+> renderValue fieldKind fieldSeed P.<> semi]
        where initializeNested nestedIndex (nestedKind, nestedSeed) = initializeAt nestedKind nestedAccess nestedName nestedSeed
               where nestedAccess = access P.<> text "." P.<> text (tupleFieldName nestedIndex)
                     nestedName   = fieldName ++ "_field_" ++ show nestedIndex

       collectionAssignment fieldKind access fieldName fieldSeed =
         [ valueDriverInit cfg renderValue fieldKind fieldName fieldSeed
         , access <+> text "=" <+> managedValueClone fieldKind (text fieldName) P.<> semi
         , valueDriverClear cfg fieldKind fieldName
         ]

       exactAssignment KUnbounded access value =
         [ text "if" <+> parens (call "mpz_set_str" [parens (text "mpz_ptr") <+> access, doubleQuotes (integer value), text "10"] <+> text "!= 0")
                     <+> call "abort" [] P.<> semi
         ]
       exactAssignment fieldKind access value
         | isExactGMPKind cfg fieldKind
         = [ text "if" <+> parens (call "mpq_set_str" [parens (text "mpq_ptr") <+> access, doubleQuotes (integer value), text "10"] <+> text "!= 0")
                     <+> call "abort" [] P.<> semi
           , call "mpq_canonicalize" [parens (text "mpq_ptr") <+> access] P.<> semi
           ]
       exactAssignment fieldKind _ _ = error $ "SBV->C: Expected an exact tuple field, received " ++ show fieldKind
valueDriverInit cfg renderValue kind@(KList elementKind)   externalName seed
  = collectionDriverInit cfg renderValue kind elementKind externalName seed False
valueDriverInit cfg renderValue kind@(KSet elementKind)    externalName seed
  = collectionDriverInit cfg renderValue kind elementKind externalName seed (odd seed)
valueDriverInit _   renderValue kind                       externalName seed
  = text "const" <+> text (elementCType kind) <+> text externalName <+> text "=" <+> renderValue kind seed P.<> semi

-- | Release storage created by 'valueDriverInit'. Borrowed scalar and string
-- literals require no cleanup.
valueDriverClear :: CgConfig -> Kind -> String -> Doc
valueDriverClear cfg kind externalName
  | isExactGMPKind cfg kind
  = gmpDriverClear kind (text externalName)
valueDriverClear cfg kind@KTuple{} externalName
  | valueNeedsOwnership cfg kind
  = managedValueRelease kind (text "&" P.<> text externalName)
valueDriverClear _   kind@KADT{}         externalName
  | isConcreteADT kind
  = managedValueRelease kind (text "&" P.<> text externalName)
valueDriverClear cfg (KList elementKind) externalName
  = vcat [valueDriverClear cfg elementKind (collectionElementName externalName index) | index <- [0 :: Int .. collectionElementCount - 1]]
valueDriverClear cfg (KSet elementKind)  externalName
  = vcat [valueDriverClear cfg elementKind (collectionElementName externalName index) | index <- [0 :: Int .. collectionElementCount - 1]]
valueDriverClear _   _                   _            = empty

-- | Declare a deterministic borrowed list or set descriptor and its elements.
collectionDriverInit :: CgConfig -> (Kind -> Integer -> Doc) -> Kind -> Kind -> String -> Integer -> Bool -> Doc
collectionDriverInit cfg renderValue kind elementKind externalName seed isComplemented
  =  vcat (zipWith initializeElement elementNames [seed ..])
  $$ text "const" <+> text (elementCType elementKind) <+> text dataName P.<> brackets (int collectionElementCount)
       <+> text "=" <+> braces (fsep (punctuate comma (map text elementNames))) P.<> semi
  $$ text "const" <+> text (elementCType kind) <+> text externalName <+> text "="
       <+> braces (fsep (punctuate comma descriptorFields)) P.<> semi
 where elementNames     = [collectionElementName externalName index | index <- [0 :: Int .. collectionElementCount - 1]]
       dataName         = externalName ++ "_data"
       descriptorFields = [text dataName, int collectionElementCount]
                       ++ case kind of
                            KSet{} -> [text (if isComplemented then "true" else "false")]
                            _      -> []

       initializeElement = valueDriverInit cfg renderValue elementKind

-- | Return the generated name of one deterministic collection element.
collectionElementName :: String -> Int -> String
collectionElementName externalName index = externalName ++ "_element_" ++ show index

-- | Number of elements placed in each deterministic example collection.
collectionElementCount :: Int
collectionElementCount = 3

-- | Extract the fields of a tuple kind.
tupleFields :: Kind -> [Kind]
tupleFields (KTuple fields) = fields
tupleFields kind            = error $ "SBV->C: Expected a tuple kind, received " ++ show kind

-- | Render a C helper call.
call :: String -> [Doc] -> Doc
call functionName arguments = text functionName P.<> parens (fsep (punctuate comma arguments))

-- | Test whether a kind is a concrete user ADT rather than a built-in or
-- uninterpreted sort.
isConcreteADT :: Kind -> Bool
isConcreteADT kind = isADT kind && not (isRoundingMode kind) && not (isUninterpreted kind)
