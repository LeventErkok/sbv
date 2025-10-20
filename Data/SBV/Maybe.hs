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

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module Data.SBV.Maybe (
  -- * Constructing optional values
    sJust, sNothing, liftMaybe, SMaybe, sMaybe, sMaybe_, sMaybes
  -- * Destructing optionals
  , maybe
  -- * Mapping functions
  , map, map2
  -- * Scrutinizing the branches of an option
  , isNothing, isJust, fromMaybe, fromJust
  ) where

import           Prelude hiding (maybe, map)
import qualified Prelude

import Data.SBV.Client
import Data.SBV.Core.Data
import Data.SBV.Core.Model (ite, OrdSymbolic(..))

#ifdef DOCTEST
-- $setup
-- >>> import Prelude hiding (maybe, map)
-- >>> import Data.SBV
#endif

-- | Make 'Maybe' symbolic.
--
-- >>> sNothing :: SMaybe Integer
-- Nothing :: Maybe Integer
-- >>> isNothing (sNothing :: SMaybe Integer)
-- True
-- >>> isNothing (sJust (literal "nope"))
-- False
-- >>> sJust (3 :: SInteger)
-- Just 3 :: Maybe Integer
-- >>> isJust (sNothing :: SMaybe Integer)
-- False
-- >>> isJust (sJust (literal "yep"))
-- True
-- >>> prove $ \x -> isJust (sJust (x :: SInteger))
-- Q.E.D.
mkSymbolic [''Maybe]

-- | Declare a symbolic maybe.
sMaybe :: SymVal a => String -> Symbolic (SMaybe a)
sMaybe = free

-- | Declare a symbolic maybe, unnamed.
sMaybe_ :: SymVal a => Symbolic (SMaybe a)
sMaybe_ = free_

-- | Declare a list of symbolic maybes.
sMaybes :: SymVal a => [String] -> Symbolic [SMaybe a]
sMaybes = symbolics

-- | Return the value of an optional value. The default is returned if Nothing. Compare to 'fromJust'.
--
-- >>> fromMaybe 2 (sNothing :: SMaybe Integer)
-- 2 :: SInteger
-- >>> sat $ \x -> fromMaybe 2 (sJust 5 :: SMaybe Integer) .== x
-- Satisfiable. Model:
--   s0 = 5 :: Integer
-- >>> prove $ \x -> fromMaybe x (sNothing :: SMaybe Integer) .== x
-- Q.E.D.
-- >>> prove $ \x -> fromMaybe (x+1) (sJust x :: SMaybe Integer) .== x
-- Q.E.D.
fromMaybe :: SymVal a => SBV a -> SMaybe a -> SBV a
fromMaybe def = maybe def id

-- | Return the value of an optional value. The behavior is undefined if
-- passed Nothing, i.e., it can return any value. Compare to 'fromMaybe'.
--
-- >>> sat $ \x -> fromJust (sJust (literal 'a')) .== x
-- Satisfiable. Model:
--   s0 = 'a' :: Char
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
fromJust = getJust_1

-- | Construct an @SMaybe a@ from a @Maybe (SBV a)@.
--
-- >>> liftMaybe (Just (3 :: SInteger))
-- Just 3 :: Maybe Integer
-- >>> liftMaybe (Nothing :: Maybe SInteger)
-- Nothing :: Maybe Integer
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
-- >>> sat $ \x -> x .== maybe 0 (`sMod` 2) (sJust (3 :: SInteger))
-- Satisfiable. Model:
--   s0 = 1 :: Integer
-- >>> sat $ \x -> x .== maybe 0 (`sMod` 2) (sNothing :: SMaybe Integer)
-- Satisfiable. Model:
--   s0 = 0 :: Integer
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
maybe brNothing brJust ma = ite (isNothing ma) brNothing (brJust (fromJust ma))

-- | Custom 'Num' instance over 'SMaybe'
instance (Ord a, SymVal a, Num a, Num (SBV a)) => Num (SBV (Maybe a)) where
  (+)         = map2 (+)
  (-)         = map2 (-)
  (*)         = map2 (*)
  abs         = map  abs
  signum      = map  signum
  fromInteger = sJust . fromInteger

-- | Custom 'OrdSymbolic' instance over 'SMaybe'.
instance (OrdSymbolic (SBV a), SymVal a) => OrdSymbolic (SBV (Maybe a)) where
  ma .< mb = maybe sFalse (\b -> maybe sTrue (.< b) ma) mb
