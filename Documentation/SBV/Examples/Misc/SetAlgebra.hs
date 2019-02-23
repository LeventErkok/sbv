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

import Data.SBV
import Data.SBV.Set ()   -- This import shouldn't be necessary, but I can't get doctest to work otherwise. Sigh.

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV
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
