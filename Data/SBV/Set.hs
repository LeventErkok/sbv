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
        -- * Insertion
        , insert
        -- * Deletion
        , delete
        -- * Membership
        -- , member, notMember
        ) where

import Data.Proxy (Proxy(Proxy))
import qualified Data.Set as Set

import Data.SBV.Core.Data
import Data.SBV.Core.Model
import Data.SBV.Core.Symbolic (SetOp(..))

-- For doctest use only
--
-- $setup
-- >>> import Data.SBV.Core.Model
-- >>> import Data.SBV.Provers.Prover
-- >>> :set -XScopedTypeVariables

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
-- >>> fromList [5,5,5,12,12,3]
-- {3,5,12} :: {SInteger}
fromList :: forall a. SymVal a => [a] -> SSet a
fromList = SBV . SVal k . Left . CV k . CSet . RegularSet . Set.fromList . map toCV
  where ka = kindOf (Proxy @a)
        k  = KSet ka

-- | Insert an element into a set.
insert :: forall a. (Ord a, SymVal a) => SBV a -> SSet a -> SSet a
insert se ss
  -- Case 1: Constant regular set, just add it:
  | Just e <- unliteral se, Just (RegularSet rs) <- unliteral ss
  = mkS $ RegularSet $ toCV e `Set.insert` Set.map toCV rs

  -- Case 2: Constant complement set, with element in the complement, just remove it:
  | Just e <- unliteral se
  , Just (ComplementSet cs) <- unliteral ss
  , let cvE = toCV e
  , let cvS = Set.map toCV cs
  , cvE `Set.member` cvS
  = mkS $ ComplementSet $ cvE `Set.delete` cvS

  -- Otherwise, go symbolic
  | True
  = SBV $ SVal k $ Right $ cache r
  where ka = kindOf (Proxy @a)
        k  = KSet ka

        mkS = SBV . SVal k . Left . CV k . CSet

        r st = do svs <- sbvToSV st ss
                  sve <- sbvToSV st se
                  newExpr st k $ SBVApp (SetOp SetInsert) [sve, svs]

-- | Delete an element from a set.
delete :: forall a. (Ord a, SymVal a) => SBV a -> SSet a -> SSet a
delete se ss
  -- Case 1: Constant regular set, just remove it:
  | Just e <- unliteral se, Just (RegularSet rs) <- unliteral ss
  = mkS $ RegularSet $ toCV e `Set.delete` Set.map toCV rs

  -- Case 2: Constant complement set, with element missing in the complement, just add it:
  | Just e <- unliteral se
  , Just (ComplementSet cs) <- unliteral ss
  , let cvE = toCV e
  , let cvS = Set.map toCV cs
  , cvE `Set.notMember` cvS
  = mkS $ ComplementSet $ cvE `Set.insert` cvS

  -- Otherwise, go symbolic
  | True
  = SBV $ SVal k $ Right $ cache r
  where ka = kindOf (Proxy @a)
        k  = KSet ka

        mkS = SBV . SVal k . Left . CV k . CSet

        r st = do svs <- sbvToSV st ss
                  sve <- sbvToSV st se
                  newExpr st k $ SBVApp (SetOp SetDelete) [sve, svs]

{-
-- | Test for membership.
member :: SBV a -> SSet a -> SBool
member se ss
  -- Case 1: Constant regular set, just check:
  | Just e <- unliteral se, Just (RegularSet 


-- | Test for non-membership.
notMember :: SBV a -> SSet a -> SBool
notMember = notMember
  -}

{- $setEquality
We can compare sets for equality:

>>> empty .== (empty :: SSet Integer)
True
>>> full .== (full :: SSet Integer)
True
>>> full ./= (full :: SSet Integer)
False
>>> sat $ \(x::SSet (Maybe Integer)) y z -> distinct [x, y, z]
Satisfiable. Model:
  s0 = U - {Nothing} :: {Maybe Integer}
  s1 =            {} :: {Maybe Integer}
  s2 =             U :: {Maybe Integer}

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
