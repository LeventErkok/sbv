{-# language KindSignatures      #-}
{-# language Rank2Types          #-}
{-# language ScopedTypeVariables #-}
{-# language TypeApplications    #-}
{-# language TypeOperators       #-}
-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Maybe
-- Author    : Joel Burget, Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Symbolic Maybe.
-----------------------------------------------------------------------------

module Data.SBV.Maybe (
  liftMaybe, map,
  isNothing, isJust,
  maybe, just
  ) where

import           Prelude             hiding      (maybe, map)
import qualified Prelude
import           Data.Proxy          (Proxy(Proxy))
import           Data.SBV.Core.Data
import           Data.SBV.Core.Model () -- instances only


-- | Construct an @SBV (Maybe a)@ from a @Maybe a@
liftMaybe :: SymVal a => Maybe (SBV a) -> SBV (Maybe a)
liftMaybe = Prelude.maybe (literal Nothing) just

-- | Map over the 'Just' side of a 'Maybe'
map
  :: forall a b.
     (SymVal a, SymVal b)
  => (SBV a -> SBV b)
  -> SBV (Maybe a)
  -> SBV (Maybe b)
map f = maybe (literal Nothing) (just . f)

-- | Return 'sTrue' if the given symbolic value is 'Nothing', 'sFalse'
-- otherwise
isNothing :: SymVal a => SBV (Maybe a) -> SBV Bool
isNothing = maybe sTrue (const sFalse)

-- | Return 'sTrue' if the given symbolic value is 'Just', 'sFalse' otherwise
isJust :: SymVal a => SBV (Maybe a) -> SBV Bool
isJust = maybe sFalse (const sTrue)

-- | Construct an @SBV (Maybe a)@ from an @SBV a@
just :: forall a. SymVal a => SBV a -> SBV (Maybe a)
just sa
  | Just a <- unliteral sa
  = literal (Just a)
  | True
  = SBV $ SVal k $ Right $ cache res
  where k = kindOf (Proxy @(Maybe a))
        res st = do asv <- sbvToSV st sa
                    newExpr st k $ SBVApp (SumConstructor InR) [asv]

-- | Case analysis for symbolic 'Maybe's. If the value 'isNothing', return the
-- default value; if it 'isJust', apply the function.
maybe
  :: forall a b.
     (SymVal a, SymVal b)
  => SBV b
  -> (SBV a -> SBV b)
  -> SBV (Maybe a)
  -> SBV b
maybe brNothing brJust ma
  | Just (Just a) <- unliteral ma
  = brJust (literal a)
  | Just Nothing  <- unliteral ma
  = brNothing
  | True
  = SBV $ SVal kb $ Right $ cache res

  where ka = kindOf (Proxy @a)
        kb = kindOf (Proxy @b)

        res st = do mav <- sbvToSV st ma
                    isNothing' <- newExpr st KBool $ SBVApp (SumIs InL) [mav]
                    br1 <- sbvToSV st brNothing
                    br2 <- sbvToSV st $ brJust $ SBV $ SVal ka $
                      Right $ cache $ \_ -> newExpr st ka $
                        SBVApp (SumAccess InR)  [mav]
                    newExpr st kb $ SBVApp Ite [isNothing', br1, br2]
