-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Either
-- Copyright : (c) Joel Burget
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Symbolic coproduct, symbolic version of Haskell's 'Either' type.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module Data.SBV.Either (
    -- * Constructing sums
      sLeft, sRight, liftEither, SEither, sEither, sEither_, sEithers
    -- * Destructing sums
    , either
    -- * Mapping functions
    , bimap, first, second
    -- * Scrutinizing branches of a sum
    , isLeft, isRight, fromLeft, fromRight
  ) where

import           Prelude hiding (either)
import qualified Prelude

import Data.SBV.Client
import Data.SBV.Core.Data
import Data.SBV.Core.Model (ite, OrdSymbolic(..))

#ifdef DOCTEST
-- $setup
-- >>> import Prelude hiding(either)
-- >>> import Data.SBV
#endif

-- | Make 'Either' symbolic.
--
-- >>> sLeft 3 :: SEither Integer Bool
-- Left 3 :: SEither Integer Bool
-- >>> isLeft (sLeft 3 :: SEither Integer Bool)
-- True
-- >>> isLeft (sRight sTrue :: SEither Integer Bool)
-- False
-- >>> sRight sFalse :: SEither Integer Bool
-- Right False :: SEither Integer Bool
-- >>> isRight (sLeft 3 :: SEither Integer Bool)
-- False
-- >>> isRight (sRight sTrue :: SEither Integer Bool)
-- True
mkSymbolic [''Either]

-- | Declare a symbolic maybe.
sEither :: (SymVal a, SymVal b) => String -> Symbolic (SEither a b)
sEither = free

-- | Declare a symbolic maybe, unnamed.
sEither_ :: (SymVal a, SymVal b) => Symbolic (SEither a b)
sEither_ = free_

-- | Declare a list of symbolic maybes.
sEithers :: (SymVal a, SymVal b) => [String] -> Symbolic [SEither a b]
sEithers = symbolics

-- | Construct an @SEither a b@ from an @Either (SBV a) (SBV b)@
--
-- >>> liftEither (Left 3 :: Either SInteger SBool)
-- Left 3 :: SEither Integer Bool
-- >>> liftEither (Right sTrue :: Either SInteger SBool)
-- Right True :: SEither Integer Bool
liftEither :: (SymVal a, SymVal b) => Either (SBV a) (SBV b) -> SEither a b
liftEither = Prelude.either sLeft sRight

-- | Case analysis for symbolic 'Either's. If the value 'isLeft', apply the
-- first function; if it 'isRight', apply the second function.
--
-- >>> either (*2) (*3) (sLeft (3 :: SInteger))
-- 6 :: SInteger
-- >>> either (*2) (*3) (sRight (3 :: SInteger))
-- 9 :: SInteger
-- >>> let f = uninterpret "f" :: SInteger -> SInteger
-- >>> let g = uninterpret "g" :: SInteger -> SInteger
-- >>> prove $ \x -> either f g (sLeft x) .== f x
-- Q.E.D.
-- >>> prove $ \x -> either f g (sRight x) .== g x
-- Q.E.D.
either :: forall a b c. (SymVal a, SymVal b, SymVal c)
       => (SBV a -> SBV c)
       -> (SBV b -> SBV c)
       -> SEither a b
       -> SBV c
either brA brB sab = ite (isLeft sab) (brA (fromLeft sab)) (brB (fromRight sab))

-- | Map over both sides of a symbolic 'Either' at the same time
--
-- >>> let f = uninterpret "f" :: SInteger -> SInteger
-- >>> let g = uninterpret "g" :: SInteger -> SInteger
-- >>> prove $ \x -> fromLeft (bimap f g (sLeft x)) .== f x
-- Q.E.D.
-- >>> prove $ \x -> fromRight (bimap f g (sRight x)) .== g x
-- Q.E.D.
bimap :: forall a b c d.  (SymVal a, SymVal b, SymVal c, SymVal d)
      => (SBV a -> SBV b)
      -> (SBV c -> SBV d)
      -> SEither a c
      -> SEither b d
bimap brA brC = either (sLeft . brA) (sRight . brC)

-- | Map over the left side of an 'Either'
--
-- >>> let f = uninterpret "f" :: SInteger -> SInteger
-- >>> prove $ \x -> first f (sLeft x :: SEither Integer Integer) .== sLeft (f x)
-- Q.E.D.
-- >>> prove $ \x -> first f (sRight x :: SEither Integer Integer) .== sRight x
-- Q.E.D.
first :: (SymVal a, SymVal b, SymVal c) => (SBV a -> SBV b) -> SEither a c -> SEither b c
first f = bimap f id

-- | Map over the right side of an 'Either'
--
-- >>> let f = uninterpret "f" :: SInteger -> SInteger
-- >>> prove $ \x -> second f (sRight x :: SEither Integer Integer) .== sRight (f x)
-- Q.E.D.
-- >>> prove $ \x -> second f (sLeft x :: SEither Integer Integer) .== sLeft x
-- Q.E.D.
second :: (SymVal a, SymVal b, SymVal c) => (SBV b -> SBV c) -> SEither a b -> SEither a c
second = bimap id

-- | Return the value from the left component. The behavior is undefined if
-- passed a right value, i.e., it can return any value.
--
-- >>> fromLeft (sLeft (literal 'a') :: SEither Char Integer)
-- 'a' :: SChar
-- >>> prove $ \x -> fromLeft (sLeft x :: SEither Char Integer) .== (x :: SChar)
-- Q.E.D.
-- >>> sat $ \x -> x .== (fromLeft (sRight 4 :: SEither Char Integer))
-- Satisfiable. Model:
--   s0 = 'A' :: Char
--
-- Note how we get a satisfying assignment in the last case: The behavior
-- is unspecified, thus the SMT solver picks whatever satisfies the
-- constraints, if there is one.
fromLeft :: forall a b. (SymVal a, SymVal b) => SEither a b -> SBV a
fromLeft = getLeft_1

-- | Return the value from the right component. The behavior is undefined if
-- passed a left value, i.e., it can return any value.
--
-- >>> fromRight (sRight (literal 'a') :: SEither Integer Char)
-- 'a' :: SChar
-- >>> prove $ \x -> fromRight (sRight x :: SEither Char Integer) .== (x :: SInteger)
-- Q.E.D.
-- >>> sat $ \x -> x .== (fromRight (sLeft (literal 2) :: SEither Integer Char))
-- Satisfiable. Model:
--   s0 = 'A' :: Char
--
-- Note how we get a satisfying assignment in the last case: The behavior
-- is unspecified, thus the SMT solver picks whatever satisfies the
-- constraints, if there is one.
fromRight :: forall a b. (SymVal a, SymVal b) => SEither a b -> SBV b
fromRight = getRight_1

-- | Custom 'OrdSymbolic' instance over 'SEither'.
instance (OrdSymbolic (SBV a), OrdSymbolic (SBV b), SymVal a, SymVal b) => OrdSymbolic (SBV (Either a b)) where
  eab .< ecd = either (\a -> either (\c -> a .< c) (\_ -> sTrue ) ecd)
                      (\b -> either (\_ -> sFalse) (\d -> b .< d) ecd)
                      eab

{- HLint ignore module "Reduce duplication" -}
