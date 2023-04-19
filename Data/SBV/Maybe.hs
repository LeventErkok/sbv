-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Maybe
-- Copyright : (c) Joel Burget
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Symbolic option type, symbolic version of Haskell's 'Maybe' type.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module Data.SBV.Maybe (
  -- * Constructing optional values
    sJust, sNothing, liftMaybe
  -- * Destructing optionals
  , maybe
  -- * Mapping functions
  , map, map2
  -- * Scrutinizing the branches of an option
  , isNothing, isJust, fromMaybe, fromJust
  ) where

import           Prelude hiding (maybe, map)
import qualified Prelude

import Data.Proxy (Proxy(Proxy))

import Data.SBV.Core.Data
import Data.SBV.Core.Model (ite)

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Prelude hiding (maybe, map)
-- >>> import Data.SBV

-- | The symbolic 'Nothing'.
--
-- >>> sNothing :: SMaybe Integer
-- Nothing :: SMaybe Integer
sNothing :: forall a. SymVal a => SMaybe a
sNothing = SBV $ SVal k $ Left $ CV k $ CMaybe Nothing
  where k = kindOf (Proxy @(Maybe a))

-- | Check if the symbolic value is nothing.
--
-- >>> isNothing (sNothing :: SMaybe Integer)
-- True
-- >>> isNothing (sJust (literal "nope"))
-- False
isNothing :: SymVal a => SMaybe a -> SBool
isNothing = maybe sTrue (const sFalse)

-- | Construct an @SMaybe a@ from an @SBV a@.
--
-- >>> sJust (3 :: SInteger)
-- Just 3 :: SMaybe Integer
sJust :: forall a. SymVal a => SBV a -> SMaybe a
sJust sa
  | Just a <- unliteral sa
  = literal (Just a)
  | True
  = SBV $ SVal kMaybe $ Right $ cache res
  where ka     = kindOf (Proxy @a)
        kMaybe = KMaybe ka

        res st = do asv <- sbvToSV st sa
                    newExpr st kMaybe $ SBVApp (MaybeConstructor ka True) [asv]

-- | Check if the symbolic value is not nothing.
--
-- >>> isJust (sNothing :: SMaybe Integer)
-- False
-- >>> isJust (sJust (literal "yep"))
-- True
-- >>> prove $ \x -> isJust (sJust (x :: SInteger))
-- Q.E.D.
isJust :: SymVal a => SMaybe a -> SBool
isJust = maybe sFalse (const sTrue)

-- | Return the value of an optional value. The default is returned if Nothing. Compare to 'fromJust'.
--
-- >>> fromMaybe 2 (sNothing :: SMaybe Integer)
-- 2 :: SInteger
-- >>> fromMaybe 2 (sJust 5 :: SMaybe Integer)
-- 5 :: SInteger
-- >>> prove $ \x -> fromMaybe x (sNothing :: SMaybe Integer) .== x
-- Q.E.D.
-- >>> prove $ \x -> fromMaybe (x+1) (sJust x :: SMaybe Integer) .== x
-- Q.E.D.
fromMaybe :: SymVal a => SBV a -> SMaybe a -> SBV a
fromMaybe def = maybe def id

-- | Return the value of an optional value. The behavior is undefined if
-- passed Nothing, i.e., it can return any value. Compare to 'fromMaybe'.
--
-- >>> fromJust (sJust (literal 'a'))
-- 'a' :: SChar
-- >>> prove $ \x -> fromJust (sJust x) .== (x :: SChar)
-- Q.E.D.
-- >>> sat $ \x -> x .== (fromJust sNothing :: SChar)
-- Satisfiable. Model:
--   s0 = 'A' :: Char
--
-- Note how we get a satisfying assignment in the last case: The behavior
-- is unspecified, thus the SMT solver picks whatever satisfies the
-- constraints, if there is one.
fromJust :: forall a. SymVal a => SMaybe a -> SBV a
fromJust ma
  | Just (Just x) <- unliteral ma
  = literal x
  | True
  = SBV $ SVal ka $ Right $ cache res
  where ka     = kindOf (Proxy @a)
        res st = do ms <- sbvToSV st ma
                    newExpr st ka (SBVApp MaybeAccess [ms])

-- | Construct an @SMaybe a@ from a @Maybe (SBV a)@.
--
-- >>> liftMaybe (Just (3 :: SInteger))
-- Just 3 :: SMaybe Integer
-- >>> liftMaybe (Nothing :: Maybe SInteger)
-- Nothing :: SMaybe Integer
liftMaybe :: SymVal a => Maybe (SBV a) -> SMaybe a
liftMaybe = Prelude.maybe (literal Nothing) sJust

-- | Map over the 'Just' side of a 'Maybe'.
--
-- >>> prove $ \x -> fromJust (map (+1) (sJust x)) .== x+(1::SInteger)
-- Q.E.D.
-- >>> let f = uninterpret "f" :: SInteger -> SBool
-- >>> prove $ \x -> map f (sJust x) .== sJust (f x)
-- Q.E.D.
-- >>> map f sNothing .== sNothing
-- True
map :: forall a b.  (SymVal a, SymVal b)
    => (SBV a -> SBV b)
    -> SMaybe a
    -> SMaybe b
map f = maybe sNothing (sJust . f)

-- | Map over two maybe values.
map2 :: forall a b c. (SymVal a, SymVal b, SymVal c) => (SBV a -> SBV b -> SBV c) -> SMaybe a -> SMaybe b -> SMaybe c
map2 op mx my = ite (isJust mx .&& isJust my)
                    (sJust (fromJust mx `op` fromJust my))
                    sNothing

-- | Case analysis for symbolic 'Maybe's. If the value 'isNothing', return the
-- default value; if it 'isJust', apply the function.
--
-- >>> maybe 0 (`sMod` 2) (sJust (3 :: SInteger))
-- 1 :: SInteger
-- >>> maybe 0 (`sMod` 2) (sNothing :: SMaybe Integer)
-- 0 :: SInteger
-- >>> let f = uninterpret "f" :: SInteger -> SBool
-- >>> prove $ \x d -> maybe d f (sJust x) .== f x
-- Q.E.D.
-- >>> prove $ \d -> maybe d f sNothing .== d
-- Q.E.D.
maybe :: forall a b.  (SymVal a, SymVal b)
      => SBV b
      -> (SBV a -> SBV b)
      -> SMaybe a
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
                    noVal <- newExpr st KBool $ SBVApp (MaybeIs ka False) [mav]
                    newExpr st kb $ SBVApp Ite [noVal, br1, br2]

-- | Custom 'Num' instance over 'SMaybe'
instance {-# OVERLAPPING #-} (Ord a, SymVal a, Num a) => Num (SBV (Maybe a)) where
  (+)         = map2 (+)
  (-)         = map2 (-)
  (*)         = map2 (*)
  abs         = map  abs
  signum      = map  signum
  fromInteger = sJust . fromInteger
