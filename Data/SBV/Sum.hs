{-# language KindSignatures      #-}
{-# language LambdaCase          #-}
{-# language Rank2Types          #-}
{-# language ScopedTypeVariables #-}
{-# language TypeApplications    #-}
{-# language TypeOperators       #-}
-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Sum
-- Author    : Joel Burget, Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Symbolic tagged unions.
-----------------------------------------------------------------------------

module Data.SBV.Sum (
  injl, injr, liftEither, case_,
  bimap, first, second,
  isLeft, isRight
  ) where

import Data.Proxy          (Proxy(Proxy))
import Data.SBV.Core.Data
import Data.SBV.Core.Model () -- instances only

-- | Constructor labels
-- data Label (l :: Symbol) = Make

injl :: forall a b. (SymVal a, SymVal b) => SBV a -> SBV (Either a b)
injl sa
  | Just a <- unliteral sa
  = literal (Left a)
  | True
  = SBV $ SVal k $ Right $ cache res
  where k = kindOf (Proxy @(Either a b))
        res st = do asv <- sbvToSV st sa
                    newExpr st k $ SBVApp (SumConstructor False) [asv]

injr :: forall a b. (SymVal a, SymVal b) => SBV b -> SBV (Either a b)
injr sb
  | Just b <- unliteral sb
  = literal (Right b)
  | True
  = SBV $ SVal k $ Right $ cache res
  where k = kindOf (Proxy @(Either a b))
        res st = do bsv <- sbvToSV st sb
                    newExpr st k $ SBVApp (SumConstructor True) [bsv]

liftEither
  :: (SymVal a, SymVal b)
  => Either (SBV a) (SBV b)
  -> SBV (Either a b)
liftEither = \case
  Left  sa -> injl sa
  Right sb -> injr sb

bimap
  :: forall a b c d.
     (SymVal a, SymVal b, SymVal c, SymVal d)
  => (SBV a -> SBV b)
  -> (SBV c -> SBV d)
  -> SBV (Either a c)
  -> SBV (Either b d)
bimap brA brC sac = case_ sac (injl . brA) (injr . brC)

first
  :: (SymVal a, SymVal b, SymVal c)
  => (SBV a -> SBV b) -> SBV (Either a c) -> SBV (Either b c)
first f = bimap f id

second
  :: (SymVal a, SymVal b, SymVal c)
  => (SBV b -> SBV c) -> SBV (Either a b) -> SBV (Either a c)
second f = bimap id f

isLeft :: (SymVal a, SymVal b) => SBV (Either a b) -> SBV Bool
isLeft sab = case_ sab (const sTrue) (const sFalse)

isRight :: (SymVal a, SymVal b) => SBV (Either a b) -> SBV Bool
isRight sab = case_ sab (const sFalse) (const sTrue)

case_
  :: forall a b c.
     (SymVal a, SymVal b, SymVal c)
  => SBV (Either a b)
  -> (SBV a -> SBV c)
  -> (SBV b -> SBV c)
  -> SBV c
case_ sab brA brB
  | Just (Left  a) <- unliteral sab
  = brA $ literal a
  | Just (Right b) <- unliteral sab
  = brB $ literal b
  | True
  = SBV $ SVal kc $ Right $ cache res

  where ka = kindOf (Proxy @a)
        kb = kindOf (Proxy @b)
        kc = kindOf (Proxy @c)

        res st = do abv <- sbvToSV st sab
                    isLeft' <- newExpr st KBool $ SBVApp (SumIs False) [abv]
                    br1 <- sbvToSV st $ brA $ SBV $ SVal ka $ Right $
                      cache $ \_ -> newExpr st ka $
                        SBVApp (SumAccess False) [abv]
                    br2 <- sbvToSV st $ brB $ SBV $ SVal kb $ Right $
                      cache $ \_ -> newExpr st kb $
                        SBVApp (SumAccess True)  [abv]
                    newExpr st kc $ SBVApp Ite [isLeft', br1, br2]
