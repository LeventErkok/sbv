-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.Kind
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Internal data-structures for the sbv library
-----------------------------------------------------------------------------

{-# LANGUAGE    ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans   #-}

module Data.SBV.BitVectors.Kind
  ( Kind(..)
  , kindHasSign
  , constructUKind
  ) where

import qualified Data.Generics as G (Data(..), DataType, dataTypeName, dataTypeOf, tyconUQname, dataTypeConstrs, constrFields)

import Data.SBV.BitVectors.AlgReals () -- instances only

-- | Kind of symbolic value
data Kind = KBool
          | KBounded Bool Int
          | KUnbounded
          | KReal
          | KUserSort String (Either String [String], G.DataType)
          | KFloat
          | KDouble
          deriving (Eq, Ord)

instance Show Kind where
  show KBool              = "SBool"
  show (KBounded False n) = "SWord" ++ show n
  show (KBounded True n)  = "SInt"  ++ show n
  show KUnbounded         = "SInteger"
  show KReal              = "SReal"
  show (KUserSort s _)    = s
  show KFloat             = "SFloat"
  show KDouble            = "SDouble"

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
    KUserSort{}  -> False

-- | Construct an uninterpreted/enumerated kind from a piece of data; we distinguish simple enumerations as those
-- are mapped to proper SMT-Lib2 data-types; while others go completely uninterpreted
constructUKind :: forall a. (Read a, G.Data a) => a -> Kind
constructUKind a = KUserSort sortName (mbEnumFields, dataType)
  where dataType      = G.dataTypeOf a
        sortName      = G.tyconUQname . G.dataTypeName $ dataType
        constrs       = G.dataTypeConstrs dataType
        isEnumeration = not (null constrs) && all (null . G.constrFields) constrs
        mbEnumFields
         | isEnumeration = check constrs []
         | True          = Left $ sortName ++ "is not a finite non-empty enumeration"
        check []     sofar = Right $ reverse sofar
        check (c:cs) sofar = case checkConstr c of
                                Nothing -> check cs (show c : sofar)
                                Just s  -> Left $ sortName ++ "." ++ show c ++ ": " ++ s
        checkConstr c = case (reads (show c) :: [(a, String)]) of
                          ((_, "") : _)  -> Nothing
                          _              -> Just "not a nullary constructor"
