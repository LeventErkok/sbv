{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Data.SBV.Tuple where

import Data.SBV.Core.Data hiding (StrOp(..))
import Data.SBV.Core.Symbolic (svToSW)
import Data.SBV.Core.Model (HListable(..))

class (SymWord tup, SymWord a) => Field1 tup a where
  field1 :: SBV tup -> SBV a

class (SymWord tup, SymWord b) => Field2 tup b where
  field2 :: SBV tup -> SBV b

class (SymWord tup, SymWord c) => Field3 tup c where
  field3 :: SBV tup -> SBV c

instance (HListable tup, SymWord tup, SymWord a, HLTy tup ~ (a : tys))
  => Field1 tup a where
  field1 tup
    | Just (HCons a _) <- toHList <$> unliteral tup
    = literal a
    | True
    = SBV (SVal kElem (Right (cache y)))
    where kElem = kindOf (undefined :: a)
          y :: State -> IO SW
          y st = do
            sw <- svToSW st $ unSBV tup
            newExpr st kElem (SBVApp (TupleAccess 1) [sw])

instance (HListable tup, SymWord tup, SymWord b, HLTy tup ~ (a : b : tys))
  => Field2 tup b where
  field2 tup
    | Just (HCons _ (HCons b _)) <- toHList <$> unliteral tup
    = literal b
    | True
    = SBV (SVal kElem (Right (cache y)))
    where kElem = kindOf (undefined :: b)
          y :: State -> IO SW
          y st = do
            sw <- svToSW st $ unSBV tup
            newExpr st kElem (SBVApp (TupleAccess 2) [sw])

instance (HListable tup, SymWord tup, SymWord c, HLTy tup ~ (a : b : c : tys))
  => Field3 tup c where
  field3 tup
    | Just (HCons _ (HCons _ (HCons c _))) <- toHList <$> unliteral tup
    = literal c
    | True
    = SBV (SVal kElem (Right (cache y)))
    where kElem = kindOf (undefined :: c)
          y :: State -> IO SW
          y st = do
            sw <- svToSW st $ unSBV tup
            newExpr st kElem (SBVApp (TupleAccess 3) [sw])
