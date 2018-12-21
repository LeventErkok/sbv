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
field
  :: forall tup a n.
     ( HListable tup, SymWord tup, SymWord a
     , IndexType n (HListTy tup), TheResult n (HListTy tup) ~ a
     )
  => SNat n -> SBV tup -> SBV a
field n tup
  | Just a <- fromIndex n . toHList <$> unliteral tup
  = literal a
  | True
  = symbolicFieldAccess (sNatToInt n + 1) tup
  where

    sNatToInt :: SNat n' -> Int
    sNatToInt SZ      = 0
    sNatToInt (SS n') = succ (sNatToInt n')

-- | Access the first field of a tuple or @HList@.
field1
  :: ( HListable tup, SymWord tup, SymWord a
     , n ~ 'Z
     , IndexType n (HListTy tup), TheResult n (HListTy tup) ~ a
     )
  => SBV tup -> SBV a
field1 = field SZ

-- | Access the second field of a tuple or @HList@.
field2
  :: ( HListable tup, SymWord tup, SymWord a
     , n ~ 'S 'Z
     , IndexType n (HListTy tup), TheResult n (HListTy tup) ~ a
     )
  => SBV tup -> SBV a
field2 = field $ SS SZ

-- | Access the third field of a tuple or @HList@.
field3
  :: ( HListable tup, SymWord tup, SymWord a
     , n ~ 'S ('S 'Z)
     , IndexType n (HListTy tup), TheResult n (HListTy tup) ~ a
     )
  => SBV tup -> SBV a
field3 = field $ SS $ SS SZ

-- | Access the fourth field of a tuple or @HList@.
field4
  :: ( HListable tup, SymWord tup, SymWord a
     , n ~ 'S ('S ('S 'Z))
     , IndexType n (HListTy tup), TheResult n (HListTy tup) ~ a
     )
  => SBV tup -> SBV a
field4 = field $ SS $ SS $ SS SZ

-- | Access the fifth field of a tuple or @HList@.
field5
  :: ( HListable tup, SymWord tup, SymWord a
     , n ~ 'S ('S ('S ('S 'Z)))
     , IndexType n (HListTy tup), TheResult n (HListTy tup) ~ a
     )
  => SBV tup -> SBV a
field5 = field $ SS $ SS $ SS $ SS SZ

-- | Access the sixth field of a tuple or @HList@.
field6
  :: ( HListable tup, SymWord tup, SymWord a
     , n ~ 'S ('S ('S ('S ('S 'Z))))
     , IndexType n (HListTy tup), TheResult n (HListTy tup) ~ a
     )
  => SBV tup -> SBV a
field6 = field $ SS $ SS $ SS $ SS $ SS SZ

-- | Access the seventh field of a tuple or @HList@.
field7
  :: ( HListable tup, SymWord tup, SymWord a
     , n ~ 'S ('S ('S ('S ('S ('S 'Z)))))
     , IndexType n (HListTy tup), TheResult n (HListTy tup) ~ a
     )
  => SBV tup -> SBV a
field7 = field $ SS $ SS $ SS $ SS $ SS $ SS SZ

-- | Access the eighth field of a tuple or @HList@.
field8
  :: ( HListable tup, SymWord tup, SymWord a
     , n ~ 'S ('S ('S ('S ('S ('S ('S 'Z))))))
     , IndexType n (HListTy tup), TheResult n (HListTy tup) ~ a
     )
  => SBV tup -> SBV a
field8 = field $ SS $ SS $ SS $ SS $ SS $ SS $ SS SZ

symbolicFieldAccess :: forall a tup. HasKind a => Int -> SBV tup -> SBV a
symbolicFieldAccess n tup
  = SBV (SVal kElem (Right (cache y)))
  where kElem = kindOf (undefined :: a)
        y st = do
          sw <- svToSW st $ unSBV tup
          newExpr st kElem (SBVApp (TupleAccess n) [sw])
