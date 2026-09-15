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
import Data.SBV.Compilers.C.GMP        (gmpDriverAssign, gmpDriverClear, gmpDriverInit, gmpEqual, isExactGMPKind)
import Data.SBV.Compilers.C.Types      ( isConcreteADTReference, arrayStoredCloneName, arrayStoredReleaseName
                                     , constElementCType, elementCType, tupleCType, tupleFieldName
                                     , adtEqualName, adtOwnedCloneName, adtOwnedReleaseName
                                     , tupleOwnedInitName, tupleOwnedCloneName, tupleOwnedReleaseName
                                     , listCloneName, listReleaseName, listHelperName
                                     , setCloneName, setReleaseName, setHelperName
                                     , textCloneName, textReleaseName, textCompareName
                                     )
import Data.SBV.Compilers.CodeGen      (CgConfig)
import Data.SBV.Core.Data

-- | Test whether a value requires clone-and-release ownership when it crosses
-- a generated C ABI boundary. Concrete ADTs use a uniform ownership protocol,
-- including those whose resolved fields do not themselves need deep storage.
valueNeedsOwnership :: CgConfig -> Kind -> Bool
valueNeedsOwnership cfg kind
  | isExactGMPKind cfg kind = True
valueNeedsOwnership _   KString        = True
valueNeedsOwnership _   KList{}        = True
valueNeedsOwnership _   KSet{}         = True
valueNeedsOwnership _   KArray{}       = True
valueNeedsOwnership cfg (KTuple kinds) = any (valueNeedsOwnership cfg) kinds
valueNeedsOwnership _   kind@KADT{}    = isConcreteADTReference kind
valueNeedsOwnership _   KApp{}         = True
valueNeedsOwnership _   _              = False

-- | Test whether a deterministic example-driver value needs declarations or
-- initialization statements instead of a single C compound literal.
valueDriverNeedsInitialization :: CgConfig -> Kind -> Bool
valueDriverNeedsInitialization cfg kind
  | isExactGMPKind cfg kind = True
valueDriverNeedsInitialization cfg (KTuple fields)      = any (valueNeedsOwnership cfg) fields
valueDriverNeedsInitialization cfg (KList elementKind)  = valueDriverNeedsInitialization cfg elementKind
valueDriverNeedsInitialization cfg (KSet elementKind)   = valueDriverNeedsInitialization cfg elementKind
valueDriverNeedsInitialization _   KArray{}             = True
valueDriverNeedsInitialization _   kind@KADT{}          = isConcreteADTReference kind
valueDriverNeedsInitialization _   KApp{}               = True
valueDriverNeedsInitialization _   _                    = False

-- | Render equality for a scalar or recursively nested aggregate. The Boolean
-- flag selects object equality for floating-point values. Array-valued fields
-- carry an unreachable abort sentinel: operation validation rejects consumers
-- requiring extensional equality, while unused aggregate helpers may be emitted.
byValueEqual :: CgConfig -> Bool -> Kind -> Doc -> Doc -> Doc
byValueEqual cfg strong kind left right
  | isWideBV kind                             = wideBVEqual kind left right
  | isFP kind && strong                       = arbitraryFPObjectEqual kind left right
  | isFP kind                                 = arbitraryFPEqual kind left right
  | strong && (isFloat kind || isDouble kind) = nativeFPObjectEqual left right
  | isExactGMPKind cfg kind                   = gmpEqual kind left right
  | kind == KString                           = parens $ call textCompareName [left, right] <+> text "== 0"
  | isList kind                               = call (listHelperName kind "equal") [left, right]
  | isSet kind                                = call (setHelperName kind "equal") [left, right]
  | isArray kind                              = text "(abort(), false)"
  | KTuple fields <- kind                     = tupleEquality fields
  | isConcreteADTReference kind               = call (adtEqualName strong kind) [left, right]
  | True                                      = left <+> text "==" <+> right
 where tupleEquality []     = parens . fsep . punctuate comma $ [text "(void)" <+> parens left, text "(void)" <+> parens right, text "true"]
       tupleEquality fields = parens . fsep . punctuate (text " &&") $
         zipWith equalField [1 :: Int ..] fields

       equalField index fieldKind = byValueEqual cfg strong fieldKind
         (parens left  P.<> text "." P.<> text (tupleFieldName index))
         (parens right P.<> text "." P.<> text (tupleFieldName index))

-- | Deep-copy one non-GMP managed value. Exact GMP values require initialized
-- destination storage and are therefore handled by their aggregate owner.
managedValueClone :: Kind -> Doc -> Doc
managedValueClone KString value       = call textCloneName [value]
managedValueClone kind@KList{} value  = call (listCloneName kind) [value]
managedValueClone kind@KSet{} value   = call (setCloneName kind) [value]
managedValueClone kind@KArray{} value = call (arrayStoredCloneName kind) [value]
managedValueClone kind@KTuple{} value = call (tupleOwnedCloneName kind) [value]
managedValueClone kind value
  | isConcreteADTReference kind       = call (adtOwnedCloneName kind) [value]
managedValueClone kind _              = error $ "SBV->C: Expected a non-GMP managed kind, received " ++ show kind

-- | Release one non-GMP managed value through a pointer to its owned storage.
managedValueRelease :: Kind -> Doc -> Doc
managedValueRelease KString address       = call textReleaseName [address] P.<> semi
managedValueRelease kind@KList{} address  = call (listReleaseName kind) [address] P.<> semi
managedValueRelease kind@KSet{} address   = call (setReleaseName kind) [address] P.<> semi
managedValueRelease kind@KArray{} address = call (arrayStoredReleaseName kind) [address] P.<> semi
managedValueRelease kind@KTuple{} address = call (tupleOwnedReleaseName kind) [address] P.<> semi
managedValueRelease kind address
  | isConcreteADTReference kind           = call (adtOwnedReleaseName kind) [address] P.<> semi
managedValueRelease kind _                = error $ "SBV->C: Expected a non-GMP managed kind, received " ++ show kind

-- | Declare and initialize one deterministic example-driver value. Managed
-- aggregates receive unique ownership; collection descriptors themselves
-- borrow the element variables declared alongside them. The supplied
-- statement renderer constructs retained arrays and registered ADTs without
-- creating dependency cycles between the structural lowering modules.
valueDriverInit :: CgConfig -> (Kind -> Integer -> Doc) -> (Kind -> String -> Integer -> Doc) -> Kind -> String -> Integer -> Doc
valueDriverInit cfg _           _               kind                       externalName seed
  | isExactGMPKind cfg kind
  = gmpDriverInit kind (text externalName) (integer seed)
valueDriverInit cfg renderValue initializeValue kind@(KTuple fields)       externalName seed
  | valueNeedsOwnership cfg kind
  =  text (tupleCType kind) <+> text externalName P.<> semi
  $$ call (tupleOwnedInitName kind) [text "&" P.<> text externalName] P.<> semi
  $$ vcat (concat (zipWith initializeTupleField [1 :: Int ..] (zip fields [seed ..])))
 where initializeTupleField index (fieldKind, fieldSeed) = initializeAt fieldKind access fieldName fieldSeed
        where access    = text externalName P.<> text "." P.<> text (tupleFieldName index)
              fieldName = externalName ++ "_field_" ++ show index

       initializeAt fieldKind access fieldName fieldSeed
         | isExactGMPKind cfg fieldKind = exactAssignment fieldKind access fieldSeed
         | fieldKind == KString         = [access <+> text "=" <+> managedValueClone fieldKind (renderValue fieldKind fieldSeed) P.<> semi]
         | isArray fieldKind            = [ initializeValue fieldKind fieldName fieldSeed
                                          , access <+> text "=" <+> text fieldName P.<> semi
                                          ]
         | isConcreteADTReference fieldKind      = [ initializeValue fieldKind fieldName fieldSeed
                                          , access <+> text "=" <+> text fieldName P.<> semi
                                          ]
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
         [ valueDriverInit cfg renderValue initializeValue fieldKind fieldName fieldSeed
         , access <+> text "=" <+> managedValueClone fieldKind (text fieldName) P.<> semi
         , valueDriverClear cfg fieldKind fieldName
         ]

       exactAssignment fieldKind access value = gmpDriverAssign fieldKind access (integer value)
valueDriverInit cfg renderValue initializeValue kind@(KList elementKind)   externalName seed
  = collectionDriverInit cfg renderValue initializeValue kind elementKind externalName seed False
valueDriverInit cfg renderValue initializeValue kind@(KSet elementKind)    externalName seed
  = collectionDriverInit cfg renderValue initializeValue kind elementKind externalName seed (odd seed)
valueDriverInit _   _           initializeValue kind@KArray{}              externalName seed
  = initializeValue kind externalName seed
valueDriverInit _   _           initializeValue kind                       externalName seed
  | isConcreteADTReference kind
  = initializeValue kind externalName seed
valueDriverInit _   renderValue _               kind                       externalName seed
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
valueDriverClear _   kind                externalName
  | isConcreteADTReference kind
  = managedValueRelease kind (text "&" P.<> text externalName)
valueDriverClear _   kind@KArray{}       externalName
  = managedValueRelease kind (text "&" P.<> text externalName)
valueDriverClear cfg (KList elementKind) externalName
  = vcat [valueDriverClear cfg elementKind (collectionElementName externalName index) | index <- [0 :: Int .. collectionElementCount - 1]]
valueDriverClear cfg (KSet elementKind)  externalName
  = vcat [valueDriverClear cfg elementKind (collectionElementName externalName index) | index <- [0 :: Int .. collectionElementCount - 1]]
valueDriverClear _   _                   _            = empty

-- | Declare a deterministic borrowed list or set descriptor and its elements.
collectionDriverInit :: CgConfig -> (Kind -> Integer -> Doc) -> (Kind -> String -> Integer -> Doc) -> Kind -> Kind -> String -> Integer -> Bool -> Doc
collectionDriverInit cfg renderValue initializeValue kind elementKind externalName seed isComplemented
  =  vcat (zipWith initializeElement elementNames [seed ..])
  $$ text (constElementCType elementKind) <+> text dataName P.<> brackets (int collectionElementCount)
       <+> text "=" <+> braces (fsep (punctuate comma (map text elementNames))) P.<> semi
  $$ text "const" <+> text (elementCType kind) <+> text externalName <+> text "="
       <+> braces (fsep (punctuate comma descriptorFields)) P.<> semi
 where elementNames     = [collectionElementName externalName index | index <- [0 :: Int .. collectionElementCount - 1]]
       dataName         = externalName ++ "_data"
       descriptorFields = [text dataName, int collectionElementCount]
                       ++ case kind of
                            KSet{} -> [text (if isComplemented then "true" else "false")]
                            _      -> []

       initializeElement = valueDriverInit cfg renderValue initializeValue elementKind

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
