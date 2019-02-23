-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Misc.SetAlgebra
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proves various algebraic properties of sets using SBV. The properties we
-- prove all come from <http://en.wikipedia.org/wiki/Algebra_of_sets>.
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
>>> prove $ complement (empty :: SI) .== full
Q.E.D.
>>> prove $ complement (full :: SI) .== empty
Q.E.D.
-}

-- * Uniqueness of the complement
--
-- $compUnique
{- $compUnique
The complement of a set is the only set that satisfies the first two complement properties above. That
is complementation is characterized by those two laws, as we can formally establish:

>>> prove $ \(a :: SI) b -> a `union` b .== full .&& a `intersection` b .== empty .<=> b .== complement a
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

-- * De Morgan's laws
-- $deMorgan
{- $deMorgan
>>> prove $ \(a :: SI) b -> complement (a `union` b) .== complement a `intersection` complement b
Q.E.D.
>>> prove $ \(a :: SI) b -> complement (a `intersection` b) .== complement a `union` complement b
Q.E.D.
-}

-- * Inclusion is a partial order
-- $incPO
{- $incPO
Subset inclusion is a partial order, i.e., it is reflexive, antisymmetric, and transitive:

>>> prove $ \(a :: SI) -> a `isSubsetOf` a
Q.E.D.
>>> prove $ \(a :: SI) b -> a `isSubsetOf` b .&& b `isSubsetOf` a .<=> a .== b
Q.E.D.
>>> prove $ \(a :: SI) b c -> a `isSubsetOf` b .&& b `isSubsetOf` c .=> a `isSubsetOf` c
Q.E.D.
-}

-- * Joins and meets
-- $joinMeet
{- $joinMeet
>>> prove $ \(a :: SI) b -> a `isSubsetOf` (a `union` b)
Q.E.D.
>>> prove $ \(a :: SI) b c -> a `isSubsetOf` c .&& b `isSubsetOf` c .=> (a `union` b) `isSubsetOf` c
Q.E.D.
>>> prove $ \(a :: SI) b -> (a `intersection` b) `isSubsetOf` a
Q.E.D.
>>> prove $ \(a :: SI) b -> (a `intersection` b) `isSubsetOf` b
Q.E.D.
>>> prove $ \(a :: SI) b c -> c `isSubsetOf` a .&& c `isSubsetOf` b .=> c `isSubsetOf` (a `intersection` b)
Q.E.D.
-}

-- * Subset characterization
-- $subsetChar
{- $subsetChar
There are multiple equivalent ways of characterizing the subset relationship:

>>> prove $ \(a :: SI) b -> a `isSubsetOf` b .<=> a `intersection` b .== a
Q.E.D.
>>> prove $ \(a :: SI) b -> a `isSubsetOf` b .<=> a `union` b .== b
Q.E.D.
>>> prove $ \(a :: SI) b -> a `isSubsetOf` b .<=> a `difference` b .== empty
Q.E.D.
>>> prove $ \(a :: SI) b -> a `isSubsetOf` b .<=> complement b `isSubsetOf` complement a
Q.E.D.
-}
