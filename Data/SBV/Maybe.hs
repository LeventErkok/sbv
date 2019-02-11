-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Maybe
-- Copyright : (c) Joel Burget
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Symbolic option type, similar to Haskell's 'Maybe' type.
-----------------------------------------------------------------------------

{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Data.SBV.Maybe (
  -- * Constructing optional values
    sJust, sNothing, liftMaybe
  -- * Mapping functions
  , maybe, map
  -- * Scrutinizing the branches of an option
  , isNothing, isJust, fromMaybe, fromJust
  ) where

import           Prelude hiding (maybe, map)
import qualified Prelude

import Data.Proxy (Proxy(Proxy))

import Data.SBV.Core.Data
import Data.SBV.Core.Model () -- instances only

-- | The symbolic 'Nothing'
sNothing :: forall a. SymVal a => SBV (Maybe a)
sNothing = SBV $ SVal k $ Left $ CV k $ CMaybe Nothing
  where k = kindOf (Proxy @(Maybe a))

-- | Return 'sTrue' if the given symbolic value is 'Nothing', 'sFalse' otherwise
isNothing :: SymVal a => SBV (Maybe a) -> SBV Bool
isNothing = maybe sTrue (const sFalse)

-- | Construct an @SBV (Maybe a)@ from an @SBV a@
sJust :: forall a. SymVal a => SBV a -> SBV (Maybe a)
sJust sa
  | Just a <- unliteral sa
  = literal (Just a)
  | True
  = SBV $ SVal k $ Right $ cache res
  where k = kindOf (Proxy @(Maybe a))
        res st = do asv <- sbvToSV st sa
                    newExpr st k $ SBVApp MaybeConstructor [asv]

-- | Return 'sTrue' if the given symbolic value is 'Just', 'sFalse' otherwise
isJust :: SymVal a => SBV (Maybe a) -> SBV Bool
isJust = maybe sFalse (const sTrue)

fromMaybe :: SymVal a => SBV a -> SBV (Maybe a) -> SBV a
fromMaybe def = maybe def id
fromJust :: forall a. SymVal a => SBV (Maybe a) -> SBV a
fromJust ma
  | Just (Just x) <- unliteral ma
  = literal x
  | True
  = SBV $ SVal ka $ Right $ cache res
  where ka     = kindOf (Proxy @a)
        kMaybe = KMaybe ka

        -- We play the usual trick here of creating a just value
        -- and asserting equivalence under implication. This will
        -- be underspecified as required should the value
        -- received be `Nothing`.
        res st = do e   <- internalVariable st ka
                    es  <- newExpr st kMaybe (SBVApp MaybeConstructor [e])
                    let esSBV = SBV $ SVal kMaybe $ Right $ cache $ \_ -> return es
                    internalConstraint st False [] $ unSBV $ isJust ma .=> esSBV .== ma
                    return e

-- | Construct an @SBV (Maybe a)@ from a @Maybe a@
liftMaybe :: SymVal a => Maybe (SBV a) -> SBV (Maybe a)
liftMaybe = Prelude.maybe (literal Nothing) just

-- | Map over the 'Just' side of a 'Maybe'
map :: forall a b.  (SymVal a, SymVal b)
    => (SBV a -> SBV b)
    -> SBV (Maybe a)
    -> SBV (Maybe b)
map f = maybe (literal Nothing) (sJust . f)

-- | Case analysis for symbolic 'Maybe's. If the value 'isNothing', return the
-- default value; if it 'isJust', apply the function.
maybe :: forall a b.  (SymVal a, SymVal b)
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

                    let justVal = SBV $ SVal ka $ Right $ cache $ \_ -> newExpr st ka $ SBVApp MaybeAccess [mav]

                        justRes = brJust justVal

                    br1 <- sbvToSV st brNothing
                    br2 <- sbvToSV st justRes

                    -- Do we have a value?
                    noVal <- newExpr st KBool $ SBVApp (MaybeIs False) [mav]
                    newExpr st kb $ SBVApp Ite [noVal, br1, br2]
