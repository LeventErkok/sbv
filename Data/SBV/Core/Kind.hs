-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Core.Kind
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Internal data-structures for the sbv library
-----------------------------------------------------------------------------

{-# LANGUAGE    DefaultSignatures    #-}
{-# LANGUAGE    FlexibleInstances    #-}
{-# LANGUAGE    ScopedTypeVariables  #-}
{-# LANGUAGE    TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans    #-}

module Data.SBV.Core.Kind (Kind(..), HasKind(..), constructUKind) where

import qualified Data.Generics as G (Data(..), DataType, dataTypeName, dataTypeOf, tyconUQname, dataTypeConstrs, constrFields)

import Data.Int
import Data.Word
import Data.SBV.Core.AlgReals

-- | Kind of symbolic value
data Kind = KBool
          | KBounded !Bool !Int
          | KUnbounded
          | KReal
          | KUserSort String (Either String [String])  -- name. Left: uninterpreted. Right: enum constructors.
          | KFloat
          | KDouble
          | KChar
          | KString

-- | Helper for Eq/Ord instances below
kindRank :: Kind -> Either Int (Either (Bool, Int) String)
kindRank KBool           = Left 0
kindRank (KBounded  b i) = Right (Left (b, i))
kindRank KUnbounded      = Left 1
kindRank KReal           = Left 2
kindRank (KUserSort s _) = Right (Right s)
kindRank KFloat          = Left 3
kindRank KDouble         = Left 4
kindRank KChar           = Left 5
kindRank KString         = Left 6
{-# INLINE kindRank #-}

-- | We want to equate user-sorts only by name
instance Eq Kind where
  k1 == k2 = kindRank k1 == kindRank k2

-- | We want to order user-sorts only by name
instance Ord Kind where
  k1 `compare` k2 = kindRank k1 `compare` kindRank k2

instance Show Kind where
  show KBool              = "SBool"
  show (KBounded False n) = "SWord" ++ show n
  show (KBounded True n)  = "SInt"  ++ show n
  show KUnbounded         = "SInteger"
  show KReal              = "SReal"
  show (KUserSort s _)    = s
  show KFloat             = "SFloat"
  show KDouble            = "SDouble"
  show KString            = "SString"
  show KChar              = "SChar"

instance Eq  G.DataType where
   a == b = G.tyconUQname (G.dataTypeName a) == G.tyconUQname (G.dataTypeName b)

instance Ord G.DataType where
   a `compare` b = G.tyconUQname (G.dataTypeName a) `compare` G.tyconUQname (G.dataTypeName b)

-- | Does this kind represent a signed quantity?
kindHasSign :: Kind -> Bool
kindHasSign k =
  case k of
    KBool        -> False
    KBounded b _ -> b
    KUnbounded   -> True
    KReal        -> True
    KFloat       -> True
    KDouble      -> True
    KString      -> False
    KChar        -> False
    KUserSort{}  -> False

-- | Construct an uninterpreted/enumerated kind from a piece of data; we distinguish simple enumerations as those
-- are mapped to proper SMT-Lib2 data-types; while others go completely uninterpreted
constructUKind :: forall a. (Read a, G.Data a) => a -> Kind
constructUKind a = KUserSort sortName mbEnumFields
  where dataType      = G.dataTypeOf a
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
-- a 'Data' instance; this is useful for creating uninterpreted sorts. So, in
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
  isInteger       :: a -> Bool
  isUninterpreted :: a -> Bool
  isChar          :: a -> Bool
  isString        :: a -> Bool
  showType        :: a -> String
  -- defaults
  hasSign x = kindHasSign (kindOf x)
  intSizeOf x = case kindOf x of
                  KBool         -> error "SBV.HasKind.intSizeOf((S)Bool)"
                  KBounded _ s  -> s
                  KUnbounded    -> error "SBV.HasKind.intSizeOf((S)Integer)"
                  KReal         -> error "SBV.HasKind.intSizeOf((S)Real)"
                  KFloat        -> error "SBV.HasKind.intSizeOf((S)Float)"
                  KDouble       -> error "SBV.HasKind.intSizeOf((S)Double)"
                  KString       -> error "SBV.HasKind.intSizeOf((S)Double)"
                  KChar         -> error "SBV.HasKind.intSizeOf((S)Char)"
                  KUserSort s _ -> error $ "SBV.HasKind.intSizeOf: Uninterpreted sort: " ++ s
  isBoolean       x | KBool{}      <- kindOf x = True
                    | True                     = False
  isBounded       x | KBounded{}   <- kindOf x = True
                    | True                     = False
  isReal          x | KReal{}      <- kindOf x = True
                    | True                     = False
  isFloat         x | KFloat{}     <- kindOf x = True
                    | True                     = False
  isDouble        x | KDouble{}    <- kindOf x = True
                    | True                     = False
  isInteger       x | KUnbounded{} <- kindOf x = True
                    | True                     = False
  isUninterpreted x | KUserSort{}  <- kindOf x = True
                    | True                     = False
  isString        x | KString{}    <- kindOf x = True
                    | True                     = False
  isChar          x | KChar{}      <- kindOf x = True
                    | True                     = False
  showType = show . kindOf

  -- default signature for uninterpreted/enumerated kinds
  default kindOf :: (Read a, G.Data a) => a -> Kind
  kindOf = constructUKind

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
instance HasKind String  where kindOf _ = KString

instance HasKind Kind where
  kindOf = id
