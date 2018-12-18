{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Data.SBV.Tuple where

import Data.SBV.Core.Data hiding (StrOp(..))
import Data.SBV.Core.Symbolic (svToSW)
import Data.SBV.Core.Model (HListable(..))

field1
  :: forall a tup tys.
     (HListable tup, SymWord tup, SymWord a, HLTy tup ~ (a : tys))
  => SBV tup -> SBV a
field1 tup
  | Just (HCons a _) <- toHList <$> unliteral tup
  = literal a
  | True
  = symbolicFieldAccess 1 tup

field2
  :: forall a b tup tys.
     (HListable tup, SymWord tup, SymWord b, HLTy tup ~ (a : b : tys))
  => SBV tup -> SBV b
field2 tup
  | Just (HCons _ (HCons b _)) <- toHList <$> unliteral tup
  = literal b
  | True
  = symbolicFieldAccess 2 tup

field3
  :: forall a b c tup tys.
     (HListable tup, SymWord tup, SymWord c, HLTy tup ~ (a : b : c : tys))
  => SBV tup -> SBV c
field3 tup
  | Just (HCons _ (HCons _ (HCons c _))) <- toHList <$> unliteral tup
  = literal c
  | True
  = symbolicFieldAccess 3 tup

field4
  :: forall a b c d tup tys.
     (HListable tup, SymWord tup, SymWord d, HLTy tup ~ (a : b : c : d : tys))
  => SBV tup -> SBV d
field4 tup
  | Just (HCons _ (HCons _ (HCons _ (HCons d _)))) <- toHList <$> unliteral tup
  = literal d
  | True
  = symbolicFieldAccess 4 tup

field5
  :: forall a b c d e tup tys.
     ( HListable tup, SymWord tup, SymWord e
     , HLTy tup ~ (a : b : c : d : e : tys)
     )
  => SBV tup -> SBV e
field5 tup
  | Just (HCons _ (HCons _ (HCons _ (HCons _ (HCons e _)))))
    <- toHList <$> unliteral tup
  = literal e
  | True
  = symbolicFieldAccess 5 tup

field6
  :: forall a b c d e f tup tys.
     ( HListable tup, SymWord tup, SymWord f
     , HLTy tup ~ (a : b : c : d : e : f : tys)
     )
  => SBV tup -> SBV f
field6 tup
  | Just (HCons _ (HCons _ (HCons _ (HCons _ (HCons _ (HCons f _))))))
    <- toHList <$> unliteral tup
  = literal f
  | True
  = symbolicFieldAccess 6 tup

field7
  :: forall a b c d e f g tup tys.
     ( HListable tup, SymWord tup, SymWord g
     , HLTy tup ~ (a : b : c : d : e : f : g : tys)
     )
  => SBV tup -> SBV g
field7 tup
  | Just (HCons _ (HCons _ (HCons _ (HCons _ (HCons _ (HCons _ (HCons g _)))))))
    <- toHList <$> unliteral tup
  = literal g
  | True
  = symbolicFieldAccess 7 tup

field8
  :: forall a b c d e f g h tup tys.
     ( HListable tup, SymWord tup, SymWord h
     , HLTy tup ~ (a : b : c : d : e : f : g : h : tys)
     )
  => SBV tup -> SBV h
field8 tup
  | Just (HCons _ (HCons _ (HCons _ (HCons _ (HCons _ (HCons _ (HCons _
      (HCons h _))))))))
    <- toHList <$> unliteral tup
  = literal h
  | True
  = symbolicFieldAccess 8 tup

symbolicFieldAccess :: forall a tup. HasKind a => Int -> SBV tup -> SBV a
symbolicFieldAccess n tup
  = SBV (SVal kElem (Right (cache y)))
  where kElem = kindOf (undefined :: a)
        y st = do
          sw <- svToSW st $ unSBV tup
          newExpr st kElem (SBVApp (TupleAccess n) [sw])
