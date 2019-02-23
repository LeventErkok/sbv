-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Misc.SetAlgebra
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proves various algebraic properties of sets using SBV.
-----------------------------------------------------------------------------

module Documentation.SBV.Examples.Misc.SetAlgebra where

import Data.SBV hiding (complement)
import Data.SBV.Set ()   -- This import shouldn't be necessary, but I can't get doctest to work otherwise. Sigh.

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV hiding (complement)
-- >>> import Data.SBV.Set
-- >>> :set -XScopedTypeVariables

-- | Abbreviation for set of integers. For convenience only in monomorphising the properties.
type SI = SSet Integer

-- * Commutativity
-- $commutativity
{- $commutativity
>>> prove $ \(a :: SI) b -> a `union` b .== b `union` a
Q.E.D.
>>> prove $ \(a :: SI) b -> a `intersection` b .== b `intersection` a
Q.E.D.
-}

-- * Associativity
-- $associativity
{- $associativity
>>> prove $ \(a :: SI) b c -> a `union` (b `union` c) .== (a `union` b) `union` c
Q.E.D.
>>> prove $ \(a :: SI) b c -> a `intersection` (b `intersection` c) .== (a `intersection` b) `intersection` c
Q.E.D.
-}

-- * Distributivity
-- $distributivity
{- $distributivity
>>> prove $ \(a :: SI) b c -> a `union` (b `intersection` c) .== (a `union` b) `intersection` (a `union` c)
Q.E.D.
>>> prove $ \(a :: SI) b c -> a `intersection` (b `union` c) .== (a `intersection` b) `union` (a `intersection` c)
Q.E.D.
-}

-- * Identity properties
-- $identity
{- $identity
>>> prove $ \(a :: SI) -> a `union` empty .== a
Q.E.D.
>>> prove $ \(a :: SI) -> a `intersection` full .== a
Q.E.D.
-}

-- * Complement properties
-- $complement
{- $complement
>>> prove $ \(a :: SI) -> a `union` complement a .== full
Q.E.D.
>>> prove $ \(a :: SI) -> a `intersection` complement a .== empty
Q.E.D.
>>> prove $ \(a :: SI) -> complement (complement a) .== a
Q.E.D.
-}

-- * Idempotency
-- $idempotent
{- $idempotent
>>> prove $ \(a :: SI) -> a `union` a .== a
Q.E.D.
>>> prove $ \(a :: SI) -> a `intersection` a .== a
Q.E.D.
-}

-- * Domination properties
-- $domination
{- $domination
>>> prove $ \(a :: SI) -> a `union` full .== full
Q.E.D.
>>> prove $ \(a :: SI) -> a `intersection` empty .== empty
Q.E.D.
-}

-- * Absorption properties
-- $absorption
{- $absorption
>>> prove $ \(a :: SI) b -> a `union` (a `intersection` b) .== a
Q.E.D.
>>> prove $ \(a :: SI) b -> a `intersection` (a `union` b) .== a
Q.E.D.
-}

-- * Intersection and set difference
-- $intdiff
{- $intdiff
>>> prove $ \(a :: SI) b -> a `intersection` b .== a `difference` (a `difference` b)
Q.E.D.
-}
