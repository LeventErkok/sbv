-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Core.Kind
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Internal data-structures for the sbv library
-----------------------------------------------------------------------------

{-# LANGUAGE DefaultSignatures   #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ViewPatterns        #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.SBV.Core.Kind (Kind(..), HasKind(..), constructUKind, smtType, hasUninterpretedSorts, showBaseKind, needsFlattening) where

import qualified Data.Generics as G (Data(..), DataType, dataTypeName, dataTypeOf, tyconUQname, dataTypeConstrs, constrFields)

import Data.Char (isSpace)

import Data.Int
import Data.Word
import Data.SBV.Core.AlgReals

import Data.Proxy

import Data.List (isPrefixOf, intercalate)

import Data.Typeable (Typeable)

import Data.SBV.Utils.Lib (isKString)

-- | Kind of symbolic value
data Kind = KBool
          | KBounded !Bool !Int
          | KUnbounded
          | KReal
          | KUninterpreted String (Either String [String])  -- name. Left: uninterpreted. Right: enum constructors.
          | KFloat
          | KDouble
          | KChar
          | KString
          | KList Kind
          | KSet  Kind
          | KTuple [Kind]
          | KMaybe  Kind
          | KEither Kind Kind
          deriving (Eq, Ord)

-- | The interesting about the show instance is that it can tell apart two kinds nicely; since it conveniently
-- ignores the enumeration constructors. Also, when we construct a 'KUninterpreted', we make sure we don't use any of
-- the reserved names; see 'constructUKind' for details.
instance Show Kind where
  show KBool                = "SBool"
  show (KBounded False n)   = "SWord" ++ show n
  show (KBounded True n)    = "SInt"  ++ show n
  show KUnbounded           = "SInteger"
  show KReal                = "SReal"
  show (KUninterpreted s _) = s
  show KFloat               = "SFloat"
  show KDouble              = "SDouble"
  show KString              = "SString"
  show KChar                = "SChar"
  show (KList e)            = "[" ++ show e ++ "]"
  show (KSet  e)            = "{" ++ show e ++ "}"
  show (KTuple m)           = "(" ++ intercalate ", " (show <$> m) ++ ")"
  show (KMaybe k)           = "SMaybe "  ++ kindParen (showBaseKind k)
  show (KEither k1 k2)      = "SEither " ++ kindParen (showBaseKind k1) ++ " " ++ kindParen (showBaseKind k2)

-- | A version of show for kinds that says Bool instead of SBool
showBaseKind :: Kind -> String
showBaseKind = sh
  where sh k@KBool             = noS (show k)
        sh k@KBounded{}        = noS (show k)
        sh k@KUnbounded        = noS (show k)
        sh k@KReal             = noS (show k)
        sh k@KUninterpreted{}  = show k     -- Leave user-sorts untouched!
        sh k@KFloat            = noS (show k)
        sh k@KDouble           = noS (show k)
        sh k@KChar             = noS (show k)
        sh k@KString           = noS (show k)
        sh (KList k)           = "[" ++ sh k ++ "]"
        sh (KSet k)            = "{" ++ sh k ++ "}"
        sh (KTuple ks)         = "(" ++ intercalate ", " (map sh ks) ++ ")"
        sh (KMaybe k)          = "Maybe "  ++ kindParen (sh k)
        sh (KEither k1 k2)     = "Either " ++ kindParen (sh k1) ++ " " ++ kindParen (sh k2)

        -- Drop the initial S if it's there
        noS ('S':s) = s
        noS s       = s

-- | Put parens if necessary. This test is rather crummy, but seems to work ok
kindParen :: String -> String
kindParen s@('[':_) = s
kindParen s@('(':_) = s
kindParen s | any isSpace s = '(' : s ++ ")"
            | True          = s

-- | How the type maps to SMT land
smtType :: Kind -> String
smtType KBool                = "Bool"
smtType (KBounded _ sz)      = "(_ BitVec " ++ show sz ++ ")"
smtType KUnbounded           = "Int"
smtType KReal                = "Real"
smtType KFloat               = "(_ FloatingPoint  8 24)"
smtType KDouble              = "(_ FloatingPoint 11 53)"
smtType KString              = "String"
smtType KChar                = "(_ BitVec 8)"
smtType (KList k)            = "(Seq "   ++ smtType k ++ ")"
smtType (KSet  k)            = "(Array " ++ smtType k ++ " Bool)"
smtType (KUninterpreted s _) = s
smtType (KTuple [])          = "SBVTuple0"
smtType (KTuple kinds)       = "(SBVTuple" ++ show (length kinds) ++ " " ++ unwords (smtType <$> kinds) ++ ")"
smtType (KMaybe k)           = "(SBVMaybe " ++ smtType k ++ ")"
smtType (KEither k1 k2)      = "(SBVEither "  ++ smtType k1 ++ " " ++ smtType k2 ++ ")"

instance Eq  G.DataType where
   a == b = G.tyconUQname (G.dataTypeName a) == G.tyconUQname (G.dataTypeName b)

instance Ord G.DataType where
   a `compare` b = G.tyconUQname (G.dataTypeName a) `compare` G.tyconUQname (G.dataTypeName b)

-- | Does this kind represent a signed quantity?
kindHasSign :: Kind -> Bool
kindHasSign = \case KBool            -> False
                    KBounded b _     -> b
                    KUnbounded       -> True
                    KReal            -> True
                    KFloat           -> True
                    KDouble          -> True
                    KUninterpreted{} -> False
                    KString          -> False
                    KChar            -> False
                    KList{}          -> False
                    KSet{}           -> False
                    KTuple{}         -> False
                    KMaybe{}         -> False
                    KEither{}        -> False

-- | Construct an uninterpreted/enumerated kind from a piece of data; we distinguish simple enumerations as those
-- are mapped to proper SMT-Lib2 data-types; while others go completely uninterpreted
constructUKind :: forall a. (Read a, G.Data a) => a -> Kind
constructUKind a
  | any (`isPrefixOf` sortName) badPrefixes
  = error $ "Data.SBV: Cannot construct user-sort with name: " ++ show sortName ++ ": Must not start with any of " ++ intercalate ", " badPrefixes
  | True
  = KUninterpreted sortName mbEnumFields
  where -- make sure we don't step on ourselves:
        badPrefixes   = ["SBool", "SWord", "SInt", "SInteger", "SReal", "SFloat", "SDouble", "SString", "SChar", "["]

        dataType      = G.dataTypeOf a
        sortName      = G.tyconUQname . G.dataTypeName $ dataType
        constrs       = G.dataTypeConstrs dataType
        isEnumeration = not (null constrs) && all (null . G.constrFields) constrs
        mbEnumFields
         | isEnumeration = check constrs []
         | True          = Left $ sortName ++ " is not a finite non-empty enumeration"
        check []     sofar = Right $ reverse sofar
        check (c:cs) sofar = case checkConstr c of
                                Nothing -> check cs (show c : sofar)
                                Just s  -> Left $ sortName ++ "." ++ show c ++ ": " ++ s
        checkConstr c = case (reads (show c) :: [(a, String)]) of
                          ((_, "") : _)  -> Nothing
                          _              -> Just "not a nullary constructor"

-- | A class for capturing values that have a sign and a size (finite or infinite)
-- minimal complete definition: kindOf, unless you can take advantage of the default
-- signature: This class can be automatically derived for data-types that have
-- a 'G.Data' instance; this is useful for creating uninterpreted sorts. So, in
-- reality, end users should almost never need to define any methods.
class HasKind a where
  kindOf          :: a -> Kind
  hasSign         :: a -> Bool
  intSizeOf       :: a -> Int
  isBoolean       :: a -> Bool
  isBounded       :: a -> Bool   -- NB. This really means word/int; i.e., Real/Float will test False
  isReal          :: a -> Bool
  isFloat         :: a -> Bool
  isDouble        :: a -> Bool
  isUnbounded     :: a -> Bool
  isUninterpreted :: a -> Bool
  isChar          :: a -> Bool
  isString        :: a -> Bool
  isList          :: a -> Bool
  isSet           :: a -> Bool
  isTuple         :: a -> Bool
  isMaybe         :: a -> Bool
  isEither        :: a -> Bool
  showType        :: a -> String
  -- defaults
  hasSign x = kindHasSign (kindOf x)

  intSizeOf x = case kindOf x of
                  KBool              -> error "SBV.HasKind.intSizeOf((S)Bool)"
                  KBounded _ s       -> s
                  KUnbounded         -> error "SBV.HasKind.intSizeOf((S)Integer)"
                  KReal              -> error "SBV.HasKind.intSizeOf((S)Real)"
                  KFloat             -> error "SBV.HasKind.intSizeOf((S)Float)"
                  KDouble            -> error "SBV.HasKind.intSizeOf((S)Double)"
                  KUninterpreted s _ -> error $ "SBV.HasKind.intSizeOf: Uninterpreted sort: " ++ s
                  KString            -> error "SBV.HasKind.intSizeOf((S)Double)"
                  KChar              -> error "SBV.HasKind.intSizeOf((S)Char)"
                  KList ek           -> error $ "SBV.HasKind.intSizeOf((S)List)" ++ show ek
                  KSet  ek           -> error $ "SBV.HasKind.intSizeOf((S)Set)"  ++ show ek
                  KTuple tys         -> error $ "SBV.HasKind.intSizeOf((S)Tuple)" ++ show tys
                  KMaybe k           -> error $ "SBV.HasKind.intSizeOf((S)Maybe)" ++ show k
                  KEither k1 k2      -> error $ "SBV.HasKind.intSizeOf((S)Either)" ++ show (k1, k2)

  isBoolean       (kindOf -> KBool{})          = True
  isBoolean       _                            = False

  isBounded       (kindOf -> KBounded{})       = True
  isBounded       _                            = False

  isReal          (kindOf -> KReal{})          = True
  isReal          _                            = False

  isFloat         (kindOf -> KFloat{})         = True
  isFloat         _                            = False

  isDouble        (kindOf -> KDouble{})        = True
  isDouble        _                            = False

  isUnbounded     (kindOf -> KUnbounded{})     = True
  isUnbounded     _                            = False

  isUninterpreted (kindOf -> KUninterpreted{}) = True
  isUninterpreted _                            = False

  isChar          (kindOf -> KChar{})          = True
  isChar          _                            = False

  isString        (kindOf -> KString{})        = True
  isString        _                            = False

  isList          (kindOf -> KList{})          = True
  isList          _                            = False

  isSet           (kindOf -> KSet{})           = True
  isSet           _                            = False

  isTuple         (kindOf -> KTuple{})         = True
  isTuple         _                            = False

  isMaybe         (kindOf -> KMaybe{})         = True
  isMaybe         _                            = False

  isEither        (kindOf -> KEither{})        = True
  isEither        _                            = False

  showType = show . kindOf

  -- default signature for uninterpreted/enumerated kinds
  default kindOf :: (Read a, G.Data a) => a -> Kind
  kindOf = constructUKind

-- | This instance allows us to use the `kindOf (Proxy @a)` idiom instead of
-- the `kindOf (undefined :: a)`, which is safer and looks more idiomatic.
instance HasKind a => HasKind (Proxy a) where
  kindOf _ = kindOf (undefined :: a)

instance HasKind Bool    where kindOf _ = KBool
instance HasKind Int8    where kindOf _ = KBounded True  8
instance HasKind Word8   where kindOf _ = KBounded False 8
instance HasKind Int16   where kindOf _ = KBounded True  16
instance HasKind Word16  where kindOf _ = KBounded False 16
instance HasKind Int32   where kindOf _ = KBounded True  32
instance HasKind Word32  where kindOf _ = KBounded False 32
instance HasKind Int64   where kindOf _ = KBounded True  64
instance HasKind Word64  where kindOf _ = KBounded False 64
instance HasKind Integer where kindOf _ = KUnbounded
instance HasKind AlgReal where kindOf _ = KReal
instance HasKind Float   where kindOf _ = KFloat
instance HasKind Double  where kindOf _ = KDouble
instance HasKind Char    where kindOf _ = KChar

-- | Do we have a completely uninterpreted sort lying around anywhere?
hasUninterpretedSorts :: Kind -> Bool
hasUninterpretedSorts KBool                        = False
hasUninterpretedSorts KBounded{}                   = False
hasUninterpretedSorts KUnbounded                   = False
hasUninterpretedSorts KReal                        = False
hasUninterpretedSorts (KUninterpreted _ (Right _)) = False  -- These are the enumerated sorts, and they are perfectly fine
hasUninterpretedSorts (KUninterpreted _ (Left  _)) = True   -- These are the completely uninterpreted sorts, which we are looking for here
hasUninterpretedSorts KFloat                       = False
hasUninterpretedSorts KDouble                      = False
hasUninterpretedSorts KChar                        = False
hasUninterpretedSorts KString                      = False
hasUninterpretedSorts (KList k)                    = hasUninterpretedSorts k
hasUninterpretedSorts (KSet k)                     = hasUninterpretedSorts k
hasUninterpretedSorts (KTuple ks)                  = any hasUninterpretedSorts ks
hasUninterpretedSorts (KMaybe k)                   = hasUninterpretedSorts k
hasUninterpretedSorts (KEither k1 k2)              = any hasUninterpretedSorts [k1, k2]

instance (Typeable a, HasKind a) => HasKind [a] where
   kindOf x | isKString @[a] x = KString
            | True             = KList (kindOf (Proxy @a))

instance HasKind Kind where
  kindOf = id

instance HasKind () where
  kindOf _ = KTuple []

instance (HasKind a, HasKind b) => HasKind (a, b) where
  kindOf _ = KTuple [kindOf (Proxy @a), kindOf (Proxy @b)]

instance (HasKind a, HasKind b, HasKind c) => HasKind (a, b, c) where
  kindOf _ = KTuple [kindOf (Proxy @a), kindOf (Proxy @b), kindOf (Proxy @c)]

instance (HasKind a, HasKind b, HasKind c, HasKind d) => HasKind (a, b, c, d) where
  kindOf _ = KTuple [kindOf (Proxy @a), kindOf (Proxy @b), kindOf (Proxy @c), kindOf (Proxy @d)]

instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e) => HasKind (a, b, c, d, e) where
  kindOf _ = KTuple [kindOf (Proxy @a), kindOf (Proxy @b), kindOf (Proxy @c), kindOf (Proxy @d), kindOf (Proxy @e)]

instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f) => HasKind (a, b, c, d, e, f) where
  kindOf _ = KTuple [kindOf (Proxy @a), kindOf (Proxy @b), kindOf (Proxy @c), kindOf (Proxy @d), kindOf (Proxy @e), kindOf (Proxy @f)]

instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f, HasKind g) => HasKind (a, b, c, d, e, f, g) where
  kindOf _ = KTuple [kindOf (Proxy @a), kindOf (Proxy @b), kindOf (Proxy @c), kindOf (Proxy @d), kindOf (Proxy @e), kindOf (Proxy @f), kindOf (Proxy @g)]

instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f, HasKind g, HasKind h) => HasKind (a, b, c, d, e, f, g, h) where
  kindOf _ = KTuple [kindOf (Proxy @a), kindOf (Proxy @b), kindOf (Proxy @c), kindOf (Proxy @d), kindOf (Proxy @e), kindOf (Proxy @f), kindOf (Proxy @g), kindOf (Proxy @h)]

instance (HasKind a, HasKind b) => HasKind (Either a b) where
  kindOf _ = KEither (kindOf (Proxy @a)) (kindOf (Proxy @b))

instance HasKind a => HasKind (Maybe a) where
  kindOf _ = KMaybe (kindOf (Proxy @a))

-- | Should we ask the solver to flatten the output? This comes in handy so output is parseable
-- Essentially, we're being conservative here and simply requesting flattening anything that has
-- some structure to it.
needsFlattening :: Kind -> Bool
needsFlattening KBool            = False
needsFlattening KBounded{}       = False
needsFlattening KUnbounded       = False
needsFlattening KReal            = False
needsFlattening KUninterpreted{} = False
needsFlattening KFloat           = False
needsFlattening KDouble          = False
needsFlattening KChar            = False
needsFlattening KString          = False
needsFlattening KList{}          = True
needsFlattening KSet{}           = True
needsFlattening KTuple{}         = True
needsFlattening KMaybe{}         = True
needsFlattening KEither{}        = True
