{-# language KindSignatures      #-}
{-# language Rank2Types          #-}
{-# language ScopedTypeVariables #-}
{-# language TypeApplications    #-}
{-# language TypeOperators       #-}
-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Either
-- Author    : Joel Burget, Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Symbolic Either.
-----------------------------------------------------------------------------

module Data.SBV.Either (
  left, right, liftEither, either,
  bimap, first, second,
  isLeft, isRight
  ) where

import           Prelude             hiding      (either)
import qualified Prelude
import           Data.Proxy          (Proxy(Proxy))
import           Data.SBV.Core.Data
import           Data.SBV.Core.Model () -- instances only


-- | Construct an @SBV (Either a b)@ from an @SBV a@
left :: forall a b. (SymVal a, SymVal b) => SBV a -> SBV (Either a b)
left sa
  | Just a <- unliteral sa
  = literal (Left a)
  | True
  = SBV $ SVal k $ Right $ cache res
  where k = kindOf (Proxy @(Either a b))
        res st = do asv <- sbvToSV st sa
                    newExpr st k $ SBVApp (SumConstructor InL) [asv]

-- | Construct an @SBV (Either a b)@ from an @SBV b@
right :: forall a b. (SymVal a, SymVal b) => SBV b -> SBV (Either a b)
right sb
  | Just b <- unliteral sb
  = literal (Right b)
  | True
  = SBV $ SVal k $ Right $ cache res
  where k = kindOf (Proxy @(Either a b))
        res st = do bsv <- sbvToSV st sb
                    newExpr st k $ SBVApp (SumConstructor InR) [bsv]

-- | Construct an @SBV (Either a b)@ from an @Either a b@
liftEither
  :: (SymVal a, SymVal b)
  => Either (SBV a) (SBV b)
  -> SBV (Either a b)
liftEither = Prelude.either left right

-- | Map over both sides of a symbolic 'Either' at the same time
bimap
  :: forall a b c d.
     (SymVal a, SymVal b, SymVal c, SymVal d)
  => (SBV a -> SBV b)
  -> (SBV c -> SBV d)
  -> SBV (Either a c)
  -> SBV (Either b d)
bimap brA brC sac = either sac (left . brA) (right . brC)

-- | Map over the left side of an 'Either'
first
  :: (SymVal a, SymVal b, SymVal c)
  => (SBV a -> SBV b) -> SBV (Either a c) -> SBV (Either b c)
first f = bimap f id

-- | Map over the right side of an 'Either'
second
  :: (SymVal a, SymVal b, SymVal c)
  => (SBV b -> SBV c) -> SBV (Either a b) -> SBV (Either a c)
second = bimap id

-- | Return 'sTrue' if the given symbolic value is 'Left', 'sFalse' otherwise
isLeft :: (SymVal a, SymVal b) => SBV (Either a b) -> SBV Bool
isLeft sab = either sab (const sTrue) (const sFalse)

-- | Return 'sTrue' if the given symbolic value is 'Right', 'sFalse' otherwise
isRight :: (SymVal a, SymVal b) => SBV (Either a b) -> SBV Bool
isRight sab = either sab (const sFalse) (const sTrue)

-- | Case analysis for symbolic 'Either's. If the value 'isLeft', apply the
-- first function; if it 'isRight', apply the second function.
either
  :: forall a b c.
     (SymVal a, SymVal b, SymVal c)
  => SBV (Either a b)
  -> (SBV a -> SBV c)
  -> (SBV b -> SBV c)
  -> SBV c
either sab brA brB
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
                    isLeft' <- newExpr st KBool $ SBVApp (SumIs InL) [abv]
                    br1 <- sbvToSV st $ brA $ SBV $ SVal ka $ Right $
                      cache $ \_ -> newExpr st ka $
                        SBVApp (SumAccess InL) [abv]
                    br2 <- sbvToSV st $ brB $ SBV $ SVal kb $ Right $
                      cache $ \_ -> newExpr st kb $
                        SBVApp (SumAccess InR) [abv]
                    newExpr st kc $ SBVApp Ite [isLeft', br1, br2]
