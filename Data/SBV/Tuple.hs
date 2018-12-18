{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Tuple where

import Data.SBV.Core.Data hiding (StrOp(..))
import Data.SBV.Core.Symbolic (svToSW)

class (SymWord tup, SymWord a) => Field1 tup a | tup -> a where
  field1 :: SBV tup -> SBV a

class (SymWord tup, SymWord b) => Field2 tup b | tup -> b where
  field2 :: SBV tup -> SBV b

class (SymWord tup, SymWord c) => Field3 tup c | tup -> c where
  field3 :: SBV tup -> SBV c

instance (SymWord (a, b), SymWord a) => Field1 (a, b) a where
  field1 tup
    | Just (a, _) <- unliteral tup
    = literal a
    | True
    = SBV (SVal kElem (Right (cache y)))
    where kElem = kindOf (undefined :: a)
          y :: State -> IO SW
          y st = do
            sw <- svToSW st $ unSBV tup
            newExpr st kElem (SBVApp (TupleAccess 1) [sw])

instance (SymWord (a, b, c), SymWord a) => Field1 (a, b, c) a where
  field1 tup
    | Just (a, _, _) <- unliteral tup
    = literal a
    | True
    = SBV (SVal kElem (Right (cache y)))
    where kElem = kindOf (undefined :: a)
          y :: State -> IO SW
          y st = do
            sw <- svToSW st $ unSBV tup
            newExpr st kElem (SBVApp (TupleAccess 1) [sw])

instance (SymWord (a, b), SymWord b) => Field2 (a, b) b where
  field2 tup
    | Just (_, b) <- unliteral tup
    = literal b
    | True
    = SBV (SVal kElem (Right (cache y)))
    where kElem = kindOf (undefined :: b)
          y :: State -> IO SW
          y st = do
            sw <- svToSW st $ unSBV tup
            newExpr st kElem (SBVApp (TupleAccess 2) [sw])

instance (SymWord (a, b, c), SymWord b) => Field2 (a, b, c) b where
  field2 tup
    | Just (_, b, _) <- unliteral tup
    = literal b
    | True
    = SBV (SVal kElem (Right (cache y)))
    where kElem = kindOf (undefined :: b)
          y :: State -> IO SW
          y st = do
            sw <- svToSW st $ unSBV tup
            newExpr st kElem (SBVApp (TupleAccess 2) [sw])
