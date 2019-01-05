-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tuple
-- Author    : Joel Burget, Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Accessing symbolic tuple fields.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}

module Data.SBV.Tuple (
  -- * Natural numbers
    Nat(..), SNat(..)
  -- * Field access
  , field, field1, field2, field3, field4, field5, field6, field7, field8
  ) where

import Data.SBV.Core.Data hiding (StrOp(..))
import Data.SBV.Core.Symbolic (svToSW)
import Data.SBV.Core.Model (HListable(..))

-- | Natural numbers. These are used as an (type-level) index into a tuple or
-- @HList@.
data Nat = Z | S Nat

-- | Singleton natural numbers. These are used as an (term-level) index into a
-- tuple or @HList@.
data SNat (n :: Nat) where
  SZ ::           SNat 'Z
  SS :: SNat n -> SNat ('S n)

-- | Constraint that a given position in a tuple or @HList@ is of a given type.
class IndexType (n :: Nat) (xs :: [*]) where
  type TheResult n xs :: *
  fromIndex :: SNat n -> HList xs -> TheResult n xs

instance IndexType 'Z (x ': xs) where
  type TheResult 'Z (x ': xs) = x
  fromIndex SZ (x :% _) = x

instance IndexType n xs => IndexType ('S n) (y ': xs) where
  type TheResult ('S n) (y ': xs) = TheResult n xs
  fromIndex (SS n) (_ :% xs) = fromIndex n xs

-- | Access the @n@th field of a tuple or @HList@.
field :: forall tup a n.  (HListable tup, SymWord tup, SymWord a, IndexType n (HListTy tup), TheResult n (HListTy tup) ~ a) => SNat n -> SBV tup -> SBV a
field n = symbolicFieldAccess (sNatToInt n + 1)
  where sNatToInt :: SNat n' -> Int
        sNatToInt SZ      = 0
        sNatToInt (SS n') = succ (sNatToInt n')

-- | Access the first field of a tuple or @HList@.
field1 :: (HListable tup, SymWord tup, SymWord a, n ~ 'Z, IndexType n (HListTy tup), TheResult n (HListTy tup) ~ a) => SBV tup -> SBV a
field1 = field SZ

-- | Access the second field of a tuple or @HList@.
field2 :: (HListable tup, SymWord tup, SymWord a, n ~ 'S 'Z, IndexType n (HListTy tup), TheResult n (HListTy tup) ~ a) => SBV tup -> SBV a
field2 = field $ SS SZ

-- | Access the third field of a tuple or @HList@.
field3 :: (HListable tup, SymWord tup, SymWord a, n ~ 'S ('S 'Z), IndexType n (HListTy tup), TheResult n (HListTy tup) ~ a) => SBV tup -> SBV a
field3 = field $ SS $ SS SZ

-- | Access the fourth field of a tuple or @HList@.
field4 :: (HListable tup, SymWord tup, SymWord a, n ~ 'S ('S ('S 'Z)) , IndexType n (HListTy tup), TheResult n (HListTy tup) ~ a) => SBV tup -> SBV a
field4 = field $ SS $ SS $ SS SZ

-- | Access the fifth field of a tuple or @HList@.
field5 :: (HListable tup, SymWord tup, SymWord a, n ~ 'S ('S ('S ('S 'Z))), IndexType n (HListTy tup), TheResult n (HListTy tup) ~ a) => SBV tup -> SBV a
field5 = field $ SS $ SS $ SS $ SS SZ

-- | Access the sixth field of a tuple or @HList@.
field6 :: ( HListable tup, SymWord tup, SymWord a, n ~ 'S ('S ('S ('S ('S 'Z)))), IndexType n (HListTy tup), TheResult n (HListTy tup) ~ a) => SBV tup -> SBV a
field6 = field $ SS $ SS $ SS $ SS $ SS SZ

-- | Access the seventh field of a tuple or @HList@.
field7 :: (HListable tup, SymWord tup, SymWord a, n ~ 'S ('S ('S ('S ('S ('S 'Z))))), IndexType n (HListTy tup), TheResult n (HListTy tup) ~ a) => SBV tup -> SBV a
field7 = field $ SS $ SS $ SS $ SS $ SS $ SS SZ

-- | Access the eighth field of a tuple or @HList@.
field8 :: (HListable tup, SymWord tup, SymWord a, n ~ 'S ('S ('S ('S ('S ('S ('S 'Z)))))), IndexType n (HListTy tup), TheResult n (HListTy tup) ~ a) => SBV tup -> SBV a
field8 = field $ SS $ SS $ SS $ SS $ SS $ SS $ SS SZ

-- | Dynamic interface to exporting tuples, this function is not
-- exported on purpose; use it only via the 'field' functions.
symbolicFieldAccess :: SymWord a => Int -> SBV tup -> SBV a
symbolicFieldAccess i tup
  | 1 > i || i > lks
  = bad $ "Index is out of bounds, " ++ show i ++ " is outside [1," ++ show lks ++ "]"
  | SBV (SVal kval (Left v)) <- tup
  = case cwVal v of
      CWTuple vs | kval      /= ktup -> bad $ "Kind/value mismatch: "      ++ show kval
                 | length vs /= lks  -> bad $ "Value has fewer elements: " ++ show (CW kval (CWTuple vs))
                 | True              -> literal $ fromCW $ CW kElem (vs !! (i-1))
      _                              -> bad $ "Kind/value mismatch: " ++ show v
  | True
  = symAccess
  where ktup = kindOf tup

        (lks, eks) = case ktup of
                       KTuple ks -> (length ks, ks)
                       _         -> bad "Was expecting to receive a tuple!"

        kElem = eks !! (i-1)

        bad :: String -> a
        bad problem = error $ unlines [ "*** Data.SBV.field: Impossible happened"
                                      , "***   Accessing element: " ++ show i
                                      , "***   Argument kind    : " ++ show ktup
                                      , "***   Problem          : " ++ problem
                                      , "*** Please report this as a bug!"
                                      ]

        symAccess :: SBV a
        symAccess = SBV $ SVal kElem $ Right $ cache y
          where y st = do sw <- svToSW st $ unSBV tup
                          newExpr st kElem (SBVApp (TupleAccess i lks) [sw])
