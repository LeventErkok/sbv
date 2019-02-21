-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Set
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A collection of set utilities, useful when working with symbolic sets.
-- To the extent possible, the functions in this module follow those
-- of "Data.Set" so importing qualified is the recommended workflow.
--
-- Note that unlike "Data.Set", SBV sets can be infinite, represented
-- as a complement of some finite set. This means that a symbolic set
-- is either finite, or its complement is finite. Therefore, there are
-- some differences in the API from Haskell sets. For instance, you can
-- take the complement of any set, which is something you cannot do
-- in Haskell! Conversely, you cannot compute the size of a symbolic
-- set (as it can be infinite!), nor you can turn it into a list or
-- necessarily enumerate its elements.
-----------------------------------------------------------------------------

{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Data.SBV.Set (
        -- * Constructing sets
          empty, full, fromList
        -- * Equality of sets
        -- $setEquality
        ) where

import Data.Proxy (Proxy(Proxy))
import qualified Data.Set as Set

import Data.SBV.Core.Data
import Data.SBV.Core.Model

-- For doctest use only
--
-- $setup
-- >>> import Data.SBV.Core.Model
-- >>> import Data.SBV.Provers.Prover

-- | Empty set.
--
-- >>> empty :: SSet Integer
-- {} :: {SInteger}
empty :: forall a. HasKind a => SSet a
empty = SBV $ SVal k $ Left $ CV k $ CSet $ RegularSet Set.empty
  where k = KSet $ kindOf (Proxy @a)

-- | Full set.
--
-- >>> full :: SSet Integer
-- U :: {SInteger}
--
-- Note that the universal set over a type is represented by the letter @U@.
full :: forall a. HasKind a => SSet a
full = SBV $ SVal k $ Left $ CV k $ CSet $ ComplementSet Set.empty
  where k = KSet $ kindOf (Proxy @a)

-- | Conversion from a list.
--
-- >>> fromList ([] :: [Integer])
-- {} :: {SInteger}
-- >>> fromList [1,2,3]
-- {1,2,3} :: {SInteger}
-- >>> fromList [5,5,5]
-- {5} :: {SInteger}
fromList :: forall a. SymVal a => [a] -> SSet a
fromList = SBV . SVal k . Left . CV k . CSet . RegularSet . Set.fromList . map toCV
  where ka = kindOf (Proxy @a)
        k  = KSet ka

{- $setEquality
We can compare sets for equality:

>>> empty .== (empty :: SSet Integer)
True
>>> full .== (full :: SSet Integer)
True
>>> full ./= (full :: SSet Integer)
False

However, if we compare two sets that are constructed as regular or in the complement
form, we have to use a proof to establish equality:

>>> prove $ full .== (empty :: SSet Integer)
Falsifiable

The reason for this is that there is no way in Haskell to compare an infinite
set to any other set, as infinite sets are not representable at all! So, we have
to delay the judgment to the SMT solver. If you try to constant fold, you
will get:

>>> full .== (empty :: SSet Integer)
<symbolic> :: SBool

indicating that the result is a symbolic value that needs a decision
procedure to be determined!
-}
