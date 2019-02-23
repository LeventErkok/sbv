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
-- is either finite, or its complement is finite. (If the underlying
-- domain is finite, then obviously both the set itself and its complement
-- will always be finite.) Therefore, there are some differences in the API
-- from Haskell sets. For instance, you can take the complement of any set,
-- which is something you cannot do in Haskell! Conversely, you cannot compute
-- the size of a symbolic set (as it can be infinite!), nor you can turn
-- it into a list or necessarily enumerate its elements.
-----------------------------------------------------------------------------

{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Data.SBV.Set (
        -- * Constructing sets
          empty, full, singleton, fromList, complement

        -- * Equality of sets
        -- $setEquality

        -- * Insertion and deletion
        , insert, delete

        -- * Query
        , member, notMember, null, isEmpty, isFull, isUniversal, isSubsetOf, isProperSubsetOf, disjoint

        -- * Combinations
        , union, unions, difference, (\\), intersection, cartesianProduct, disjointUnion, 

        ) where

import Prelude hiding (null)

import Data.Proxy (Proxy(Proxy))
import qualified Data.Set as Set

import Data.SBV.Core.Data
import Data.SBV.Core.Model ((.==), (./=))

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

-- | Singleton list.
--
-- >>> singleton 2 :: SSet Integer
-- {2} :: {SInteger}
singleton :: forall a. (Ord a, SymVal a) => SBV a -> SSet a
singleton = (`insert` (empty :: SSet a))

-- | Conversion from a list.
--
-- >>> fromList ([] :: [Integer])
-- {} :: {SInteger}
-- >>> fromList [1,2,3]
-- {1,2,3} :: {SInteger}
-- >>> fromList [5,5,5,12,12,3]
-- {3,5,12} :: {SInteger}
fromList :: forall a. (Ord a, SymVal a) => [a] -> SSet a
fromList = literal . RegularSet . Set.fromList

-- | Complement.
--
-- >>> empty .== complement (full :: SSet Integer)
-- True
--
-- Complementing twice gets us back the original set:
--
-- >>> prove $ \(s :: SSet Integer) -> complement (complement s) .== s
-- Q.E.D.
complement :: forall a. (Ord a, SymVal a) => SSet a -> SSet a
complement ss
  | Just (RegularSet rs) <- unliteral ss
  = literal $ ComplementSet rs
  | Just (ComplementSet cs) <- unliteral ss
  = literal $ RegularSet cs
  | True
  = SBV $ SVal k $ Right $ cache r
  where k = KSet (kindOf (Proxy @a))

        r st = do svs <- sbvToSV st ss
                  newExpr st k $ SBVApp (SetOp SetComplement) [svs]

-- | Insert an element into a set.
--
-- Insertion is order independent:
--
-- >>> prove $ \x y (s :: SSet Integer) -> x `insert` (y `insert` s) .== y `insert` (x `insert` s)
-- Q.E.D.
--
-- Deletion after insertion is not necessarily identity:
--
-- >>> prove $ \x (s :: SSet Integer) -> x `delete` (x `insert` s) .== s
-- Falsifiable. Counter-example:
--   s0 =   0 :: Integer
--   s1 = {0} :: {Integer}
--
-- But the above is true if the element isn't in the set to start with:
--
-- >>> prove $ \x (s :: SSet Integer) -> x `notMember` s .=> x `delete` (x `insert` s) .== s
-- Q.E.D.
--
-- Insertion into a full set does nothing:
--
-- >>> prove $ \x -> insert x full .== (full :: SSet Integer)
-- Q.E.D.
insert :: forall a. (Ord a, SymVal a) => SBV a -> SSet a -> SSet a
insert se ss
  -- Case 1: Constant regular set, just add it:
  | Just e <- unliteral se, Just (RegularSet rs) <- unliteral ss
  = literal $ RegularSet $ e `Set.insert` rs

  -- Case 2: Constant complement set, with element in the complement, just remove it:
  | Just e <- unliteral se, Just (ComplementSet cs) <- unliteral ss, e `Set.member` cs
  = literal $ ComplementSet $ e `Set.delete` cs

  -- Otherwise, go symbolic
  | True
  = SBV $ SVal k $ Right $ cache r
  where ka = kindOf (Proxy @a)
        k  = KSet ka

        r st = do svs <- sbvToSV st ss
                  sve <- sbvToSV st se
                  newExpr st k $ SBVApp (SetOp SetInsert) [sve, svs]

-- | Delete an element from a set.
--
-- Deletion is order independent:
--
-- >>> prove $ \x y (s :: SSet Integer) -> x `delete` (y `delete` s) .== y `delete` (x `delete` s)
-- Q.E.D.
--
-- Insertion after deletion is not necessarily identity:
--
-- >>> prove $ \x (s :: SSet Integer) -> x `insert` (x `delete` s) .== s
-- Falsifiable. Counter-example:
--   s0 =  0 :: Integer
--   s1 = {} :: {Integer}
--
-- But the above is true if the element is in the set to start with:
--
-- >>> prove $ \x (s :: SSet Integer) -> x `member` s .=> x `insert` (x `delete` s) .== s
-- Q.E.D.
--
-- Deletion from an empty set does nothing:
--
-- >>> prove $ \x -> delete x empty .== (empty :: SSet Integer)
-- Q.E.D.
delete :: forall a. (Ord a, SymVal a) => SBV a -> SSet a -> SSet a
delete se ss
  -- Case 1: Constant regular set, just remove it:
  | Just e <- unliteral se, Just (RegularSet rs) <- unliteral ss
  = literal $ RegularSet $ e `Set.delete` rs

  -- Case 2: Constant complement set, with element missing in the complement, just add it:
  | Just e <- unliteral se, Just (ComplementSet cs) <- unliteral ss, e `Set.notMember` cs
  = literal $ ComplementSet $ e `Set.insert` cs

  -- Otherwise, go symbolic
  | True
  = SBV $ SVal k $ Right $ cache r
  where ka = kindOf (Proxy @a)
        k  = KSet ka

        r st = do svs <- sbvToSV st ss
                  sve <- sbvToSV st se
                  newExpr st k $ SBVApp (SetOp SetDelete) [sve, svs]

-- | Test for membership.
--
-- >>> prove $ \x -> x `member` singleton (x :: SInteger)
-- Q.E.D.
--
-- >>> prove $ \x (s :: SSet Integer) -> x `member` (x `insert` s)
-- Q.E.D.
--
-- >>> prove $ \x -> x `member` (full :: SSet Integer)
-- Q.E.D.
member :: (Ord a, SymVal a) => SBV a -> SSet a -> SBool
member se ss
  -- Case 1: Constant regular set, just check:
  | Just e <- unliteral se, Just (RegularSet rs) <- unliteral ss
  = literal $ e `Set.member` rs

  -- Case 2: Constant complement set, check for non-member
  | Just e <- unliteral se, Just (ComplementSet cs) <- unliteral ss
  = literal $ e `Set.notMember` cs

  -- Otherwise, go symbolic
  | True
  = SBV $ SVal KBool $ Right $ cache r
  where r st = do svs <- sbvToSV st ss
                  sve <- sbvToSV st se
                  newExpr st KBool $ SBVApp (SetOp SetMember) [sve, svs]

-- | Test for non-membership.
--
-- >>> prove $ \x -> x `notMember` observe "set" (singleton (x :: SInteger))
-- Falsifiable. Counter-example:
--   set = {0} :: {Integer}
--   s0  =   0 :: Integer
--
-- >>> prove $ \x (s :: SSet Integer) -> x `notMember` (x `delete` s)
-- Q.E.D.
--
-- >>> prove $ \x -> x `notMember` (empty :: SSet Integer)
-- Q.E.D.
notMember :: (Ord a, SymVal a) => SBV a -> SSet a -> SBool
notMember se ss = sNot $ member se ss

-- | Is this the empty set?
--
-- >>> null (empty :: SSet Integer)
-- True
--
-- >>> prove $ \x -> null (x `delete` singleton (x :: SInteger))
-- Q.E.D.
--
-- >>> prove $ null (full :: SSet Integer)
-- Falsifiable
--
-- Note how we have to call `Data.SBV.prove` in the last case since dealing
-- with infinite sets requires a call to the solver and cannot be
-- constant folded.
null :: HasKind a => SSet a -> SBool
null = (.== empty)

-- | Synonym for 'Data.SBV.Set.null'.
isEmpty :: HasKind a => SSet a -> SBool
isEmpty = null

-- | Is this the full set?
--
-- >>> prove $ isFull (empty :: SSet Integer)
-- Falsifiable
--
-- >>> prove $ \x -> isFull (observe "set" (x `delete` (full :: SSet Integer)))
-- Falsifiable. Counter-example:
--   set = U - {0} :: {Integer}
--   s0  =       0 :: Integer
--
-- >>> isFull (full :: SSet Integer)
-- True
--
-- Note how we have to call `Data.SBV.prove` in the first case since dealing
-- with infinite sets requires a call to the solver and cannot be
-- constant folded.
isFull :: HasKind a => SSet a -> SBool
isFull = (.== full)

-- | Synonym for 'Data.SBV.Set.isFull'.
isUniversal :: HasKind a => SSet a -> SBool
isUniversal = isFull

-- | Subset test.
--
-- >>> prove $ empty `isSubsetOf` (full :: SSet Integer)
-- Q.E.D.
--
-- >>> prove $ \x (s :: SSet Integer) -> s `isSubsetOf` (x `insert` s)
-- Q.E.D.
--
-- >>> prove $ \x (s :: SSet Integer) -> (x `delete` s) `isSubsetOf` s
-- Q.E.D.
isSubsetOf :: (Ord a, SymVal a) => SSet a -> SSet a -> SBool
isSubsetOf sa sb
  -- Case 1: Constant regular sets, just check:
  | Just (RegularSet a) <- unliteral sa, Just (RegularSet b) <- unliteral sb
  = literal $ a `Set.isSubsetOf` b

  -- Case 2: Constant complement sets, check in the reverse direction:
  | Just (ComplementSet a) <- unliteral sa, Just (ComplementSet b) <- unliteral sb
  = literal $ b `Set.isSubsetOf` a

  -- Otherwise, go symbolic
  | True
  = SBV $ SVal KBool $ Right $ cache r
  where r st = do sva <- sbvToSV st sa
                  svb <- sbvToSV st sb
                  newExpr st KBool $ SBVApp (SetOp SetSubset) [sva, svb]

-- | Proper subset test.
--
-- >>> prove $ empty `isProperSubsetOf` (full :: SSet Integer)
-- Q.E.D.
--
-- >>> prove $ \x (s :: SSet Integer) -> s `isProperSubsetOf` (x `insert` s)
-- Falsifiable. Counter-example:
--   s0 =       0 :: Integer
--   s1 = U - {1} :: {Integer}
--
-- >>> prove $ \x (s :: SSet Integer) -> x `notMember` s .=> s `isProperSubsetOf` (x `insert` s)
-- Q.E.D.
--
-- >>> prove $ \x (s :: SSet Integer) -> (x `delete` s) `isProperSubsetOf` s
-- Falsifiable. Counter-example:
--   s0 =   0 :: Integer
--   s1 = {1} :: {Integer}
--
-- >>> prove $ \x (s :: SSet Integer) -> x `member` s .=> (x `delete` s) `isProperSubsetOf` s
-- Q.E.D.
isProperSubsetOf :: (Ord a, SymVal a) => SSet a -> SSet a -> SBool
isProperSubsetOf a b = a `isSubsetOf` b .&& a ./= b

-- | Disjoint test.
disjoint :: SSet a -> SSet a -> SBool
disjoint = error "TBD: disjoint"

-- | Union.
union :: SSet a -> SSet a -> SSet a
union = error "TBD: union"

-- | Unions.
unions :: [SSet a] -> SSet a
unions = error "TBD: unions"

-- | Intersection.
intersection :: SSet a -> SSet a -> SSet a
intersection = error "TBD: union"

-- | Difference.
difference :: SSet a -> SSet a -> SSet a
difference = error "TBD: difference"

-- | Difference, synonym for 'difference'.
infixl 9 \\
(\\) :: SSet a -> SSet a -> SSet a
(\\) = difference

-- | Cartesian product.
cartesianProduct :: SSet a -> SSet a -> SSet (STuple a b)
cartesianProduct = error "TBD: cartesianProduct"

-- | Disjoin union.
disjointUnion :: SSet a -> SSet b -> SSet (SEither a b)
disjointUnion = error "TBD: disjointUnion"

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
