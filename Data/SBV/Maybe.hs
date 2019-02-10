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
  just, nothing, liftMaybe
  -- * Mapping functions
  , maybe, map
  -- * Scrutinizing the branches of an option
  , isNothing, isJust
  ) where

import           Prelude hiding (maybe, map)
import qualified Prelude

import Data.Proxy (Proxy(Proxy))

import Data.SBV.Core.Data
import Data.SBV.Core.Model () -- instances only

-- | The symbolic 'Nothing'
nothing :: forall a. SymVal a => SBV (Maybe a)
nothing = SBV $ SVal k $ Left $ CV k $ CMaybe Nothing
  where k = kindOf (Proxy @(Maybe a))

-- | Return 'sTrue' if the given symbolic value is 'Nothing', 'sFalse' otherwise
isNothing :: SymVal a => SBV (Maybe a) -> SBV Bool
isNothing = maybe sTrue (const sFalse)

-- | Construct an @SBV (Maybe a)@ from an @SBV a@
just :: forall a. SymVal a => SBV a -> SBV (Maybe a)
just sa
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

-- | Construct an @SBV (Maybe a)@ from a @Maybe a@
liftMaybe :: SymVal a => Maybe (SBV a) -> SBV (Maybe a)
liftMaybe = Prelude.maybe (literal Nothing) just

-- | Map over the 'Just' side of a 'Maybe'
map :: forall a b.  (SymVal a, SymVal b)
    => (SBV a -> SBV b)
    -> SBV (Maybe a)
    -> SBV (Maybe b)
map f = maybe (literal Nothing) (just . f)

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
