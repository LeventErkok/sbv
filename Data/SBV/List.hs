-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.List
-- Author    : Joel Burget, Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A collection of list utilities, useful when working with symbolic lists.
-- To the extent possible, the functions in this module follow those of "Data.List"
-- so importing qualified is the recommended workflow. Also, it is recommended
-- you use the @OverloadedLists@ extension to allow literal lists to
-- be used as symbolic-lists.
-----------------------------------------------------------------------------

{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Data.SBV.List (
        -- * Length, emptiness
          length, null
        -- * Deconstructing/Reconstructing
        , head, tail, uncons, init, singleton, listToListAt, elemAt, (.!!), implode, concat, (.:), nil, (.++)
        -- * Containment
        , isInfixOf, isSuffixOf, isPrefixOf
        -- * Sublists
        , take, drop, subList, replace, indexOf, offsetIndexOf
        ) where

import Prelude hiding (head, tail, init, length, take, drop, concat, null)
import qualified Prelude as P

import Data.SBV.Core.Data hiding (StrOp(..))
import Data.SBV.Core.Model

import Data.List (genericLength, genericIndex, genericDrop, genericTake)
import qualified Data.List as L (tails, isSuffixOf, isPrefixOf, isInfixOf)

import Data.Proxy

-- For doctest use only
--
-- $setup
-- >>> import Data.SBV.Provers.Prover (prove, sat)
-- >>> import Data.Int
-- >>> import Data.Word
-- >>> :set -XOverloadedLists
-- >>> :set -XScopedTypeVariables

-- | Length of a list.
--
-- >>> sat $ \(l :: SList Word16) -> length l .== 2
-- Satisfiable. Model:
--   s0 = [0,0] :: [Word16]
-- >>> sat $ \(l :: SList Word16) -> length l .< 0
-- Unsatisfiable
-- >>> prove $ \(l1 :: SList Word16) (l2 :: SList Word16) -> length l1 + length l2 .== length (l1 .++ l2)
-- Q.E.D.
length :: SymVal a => SList a -> SInteger
length = lift1 SeqLen (Just (fromIntegral . P.length))

-- | @`null` s@ is True iff the list is empty
--
-- >>> prove $ \(l :: SList Word16) -> null l .<=> length l .== 0
-- Q.E.D.
-- >>> prove $ \(l :: SList Word16) -> null l .<=> l .== []
-- Q.E.D.
null :: SymVal a => SList a -> SBool
null l
  | Just cs <- unliteral l
  = literal (P.null cs)
  | True
  = l .== literal []

-- | @`head`@ returns the first element of a list. Unspecified if the list is empty.
--
-- >>> prove $ \c -> head (singleton c) .== (c :: SInteger)
-- Q.E.D.
head :: SymVal a => SList a -> SBV a
head = (`elemAt` 0)

-- | @`tail`@ returns the tail of a list. Unspecified if the list is empty.
--
-- >>> prove $ \(h :: SInteger) t -> tail (singleton h .++ t) .== t
-- Q.E.D.
-- >>> prove $ \(l :: SList Integer) -> length l .> 0 .=> length (tail l) .== length l - 1
-- Q.E.D.
-- >>> prove $ \(l :: SList Integer) -> sNot (null l) .=> singleton (head l) .++ tail l .== l
-- Q.E.D.
tail :: SymVal a => SList a -> SList a
tail l
 | Just (_:cs) <- unliteral l
 = literal cs
 | True
 = subList l 1 (length l - 1)

-- | @`uncons` returns the pair of the head and tail. Unspecified if the list is empty.
uncons :: SymVal a => SList a -> (SBV a, SList a)
uncons l = (head l, tail l)

-- | @`init`@ returns all but the last element of the list. Unspecified if the list is empty.
--
-- >>> prove $ \(h :: SInteger) t -> init (t .++ singleton h) .== t
-- Q.E.D.
init :: SymVal a => SList a -> SList a
init l
 | Just cs@(_:_) <- unliteral l
 = literal $ P.init cs
 | True
 = subList l 0 (length l - 1)

-- | @`singleton` x@ is the list of length 1 that contains the only value @x@.
--
-- >>> prove $ \(x :: SInteger) -> head (singleton x) .== x
-- Q.E.D.
-- >>> prove $ \(x :: SInteger) -> length (singleton x) .== 1
-- Q.E.D.
singleton :: SymVal a => SBV a -> SList a
singleton = lift1 SeqUnit (Just (: []))

-- | @`listToListAt` l offset@. List of length 1 at @offset@ in @l@. Unspecified if
-- index is out of bounds.
--
-- >>> prove $ \(l1 :: SList Integer) l2 -> listToListAt (l1 .++ l2) (length l1) .== listToListAt l2 0
-- Q.E.D.
-- >>> sat $ \(l :: SList Word16) -> length l .>= 2 .&& listToListAt l 0 ./= listToListAt l (length l - 1)
-- Satisfiable. Model:
--   s0 = [0,0,32] :: [Word16]
listToListAt :: SymVal a => SList a -> SInteger -> SList a
listToListAt s offset = subList s offset 1

-- | @`elemAt` l i@ is the value stored at location @i@. Unspecified if
-- index is out of bounds.
--
-- >>> prove $ \i -> i .>= 0 .&& i .<= 4 .=> [1,1,1,1,1] `elemAt` i .== (1::SInteger)
-- Q.E.D.
-- >>> prove $ \(l :: SList Integer) i e -> l `elemAt` i .== e .=> indexOf l (singleton e) .<= i
-- Q.E.D.
elemAt :: forall a. SymVal a => SList a -> SInteger -> SBV a
elemAt l i
  | Just xs <- unliteral l, Just ci <- unliteral i, ci >= 0, ci < genericLength xs, let x = xs `genericIndex` ci
  = literal x
  | True
  = SBV (SVal kElem (Right (cache (y (l `listToListAt` i)))))
  where kElem = kindOf (Proxy @a)
        kSeq  = KList kElem
        -- This is trickier than it needs to be, but necessary since there's
        -- no SMTLib function to extract the element from a list. Instead,
        -- we form a singleton list, and assert that it is equivalent to
        -- the extracted value. See <http://github.com/Z3Prover/z3/issues/1302>
        y si st = do e <- internalVariable st kElem
                     es <- newExpr st kSeq (SBVApp (SeqOp SeqUnit) [e])
                     let esSBV = SBV (SVal kSeq (Right (cache (\_ -> return es))))
                     internalConstraint st False [] $ unSBV $ length l .> i .=> esSBV .== si
                     return e

-- | Short cut for 'elemAt'
(.!!) :: SymVal a => SList a -> SInteger -> SBV a
(.!!) = elemAt

-- | @`implode` es@ is the list of length @|es|@ containing precisely those
-- elements. Note that there is no corresponding function @explode@, since
-- we wouldn't know the length of a symbolic list.
--
-- >>> prove $ \(e1 :: SInteger) e2 e3 -> length (implode [e1, e2, e3]) .== 3
-- Q.E.D.
-- >>> prove $ \(e1 :: SInteger) e2 e3 -> map (elemAt (implode [e1, e2, e3])) (map literal [0 .. 2]) .== [e1, e2, e3]
-- Q.E.D.
implode :: SymVal a => [SBV a] -> SList a
implode = foldr ((.++) . singleton) (literal [])

-- | Concatenate two lists. See also `.++`.
concat :: SymVal a => SList a -> SList a -> SList a
concat x y | isConcretelyEmpty x = y
           | isConcretelyEmpty y = x
           | True                = lift2 SeqConcat (Just (++)) x y

-- | Prepend an element, the traditional @cons@.
infixr 5 .:
(.:) :: SymVal a => SBV a -> SList a -> SList a
a .: as = singleton a .++ as

-- | Empty list. This value has the property that it's the only list with length 0:
--
-- >>> prove $ \(l :: SList Integer) -> length l .== 0 .<=> l .== nil
-- Q.E.D.
nil :: SymVal a => SList a
nil = []

-- | Short cut for `concat`.
--
-- >>> sat $ \x y z -> length x .== 5 .&& length y .== 1 .&& x .++ y .++ z .== [1 .. 12]
-- Satisfiable. Model:
--   s0 =      [1,2,3,4,5] :: [Integer]
--   s1 =              [6] :: [Integer]
--   s2 = [7,8,9,10,11,12] :: [Integer]
infixr 5 .++
(.++) :: SymVal a => SList a -> SList a -> SList a
(.++) = concat

-- | @`isInfixOf` sub l@. Does @l@ contain the subsequence @sub@?
--
-- >>> prove $ \(l1 :: SList Integer) l2 l3 -> l2 `isInfixOf` (l1 .++ l2 .++ l3)
-- Q.E.D.
-- >>> prove $ \(l1 :: SList Integer) l2 -> l1 `isInfixOf` l2 .&& l2 `isInfixOf` l1 .<=> l1 .== l2
-- Q.E.D.
isInfixOf :: SymVal a => SList a -> SList a -> SBool
sub `isInfixOf` l
  | isConcretelyEmpty sub
  = literal True
  | True
  = lift2 SeqContains (Just (flip L.isInfixOf)) l sub -- NB. flip, since `SeqContains` takes args in rev order!

-- | @`isPrefixOf` pre l@. Is @pre@ a prefix of @l@?
--
-- >>> prove $ \(l1 :: SList Integer) l2 -> l1 `isPrefixOf` (l1 .++ l2)
-- Q.E.D.
-- >>> prove $ \(l1 :: SList Integer) l2 -> l1 `isPrefixOf` l2 .=> subList l2 0 (length l1) .== l1
-- Q.E.D.
isPrefixOf :: SymVal a => SList a -> SList a -> SBool
pre `isPrefixOf` l
  | isConcretelyEmpty pre
  = literal True
  | True
  = lift2 SeqPrefixOf (Just L.isPrefixOf) pre l

-- | @`isSuffixOf` suf l@. Is @suf@ a suffix of @l@?
--
-- >>> prove $ \(l1 :: SList Word16) l2 -> l2 `isSuffixOf` (l1 .++ l2)
-- Q.E.D.
-- >>> prove $ \(l1 :: SList Word16) l2 -> l1 `isSuffixOf` l2 .=> subList l2 (length l2 - length l1) (length l1) .== l1
-- Q.E.D.
isSuffixOf :: SymVal a => SList a -> SList a -> SBool
suf `isSuffixOf` l
  | isConcretelyEmpty suf
  = literal True
  | True
  = lift2 SeqSuffixOf (Just L.isSuffixOf) suf l

-- | @`take` len l@. Corresponds to Haskell's `take` on symbolic lists.
--
-- >>> prove $ \(l :: SList Integer) i -> i .>= 0 .=> length (take i l) .<= i
-- Q.E.D.
take :: SymVal a => SInteger -> SList a -> SList a
take i l = ite (i .<= 0)        (literal [])
         $ ite (i .>= length l) l
         $ subList l 0 i

-- | @`drop` len s@. Corresponds to Haskell's `drop` on symbolic-lists.
--
-- >>> prove $ \(l :: SList Word16) i -> length (drop i l) .<= length l
-- Q.E.D.
-- >>> prove $ \(l :: SList Word16) i -> take i l .++ drop i l .== l
-- Q.E.D.
drop :: SymVal a => SInteger -> SList a -> SList a
drop i s = ite (i .>= ls) (literal [])
         $ ite (i .<= 0)  s
         $ subList s i (ls - i)
  where ls = length s

-- | @`subList` s offset len@ is the sublist of @s@ at offset @offset@ with length @len@.
-- This function is under-specified when the offset is outside the range of positions in @s@ or @len@
-- is negative or @offset+len@ exceeds the length of @s@.
--
-- >>> prove $ \(l :: SList Integer) i -> i .>= 0 .&& i .< length l .=> subList l 0 i .++ subList l i (length l - i) .== l
-- Q.E.D.
-- >>> sat  $ \i j -> subList [1..5] i j .== ([2..4] :: SList Integer)
-- Satisfiable. Model:
--   s0 = 1 :: Integer
--   s1 = 3 :: Integer
-- >>> sat  $ \i j -> subList [1..5] i j .== ([6..7] :: SList Integer)
-- Unsatisfiable
subList :: SymVal a => SList a -> SInteger -> SInteger -> SList a
subList l offset len
  | Just c  <- unliteral l                   -- a constant list
  , Just o  <- unliteral offset              -- a constant offset
  , Just sz <- unliteral len                 -- a constant length
  , let lc = genericLength c                 -- length of the list
  , let valid x = x >= 0 && x <= lc          -- predicate that checks valid point
  , valid o                                  -- offset is valid
  , sz >= 0                                  -- length is not-negative
  , valid $ o + sz                           -- we don't overrun
  = literal $ genericTake sz $ genericDrop o c
  | True                                     -- either symbolic, or something is out-of-bounds
  = lift3 SeqSubseq Nothing l offset len

-- | @`replace` l src dst@. Replace the first occurrence of @src@ by @dst@ in @s@
--
-- >>> prove $ \l -> replace [1..5] l [6..10] .== [6..10] .=> l .== ([1..5] :: SList Word8)
-- Q.E.D.
-- >>> prove $ \(l1 :: SList Integer) l2 l3 -> length l2 .> length l1 .=> replace l1 l2 l3 .== l1
-- Q.E.D.
replace :: SymVal a => SList a -> SList a -> SList a -> SList a
replace l src dst
  | Just b <- unliteral src, P.null b   -- If src is null, simply prepend
  = dst .++ l
  | Just a <- unliteral l
  , Just b <- unliteral src
  , Just c <- unliteral dst
  = literal $ walk a b c
  | True
  = lift3 SeqReplace Nothing l src dst
  where walk haystack needle newNeedle = go haystack   -- note that needle is guaranteed non-empty here.
           where go []       = []
                 go i@(c:cs)
                  | needle `L.isPrefixOf` i = newNeedle ++ genericDrop (genericLength needle :: Integer) i
                  | True                    = c : go cs

-- | @`indexOf` l sub@. Retrieves first position of @sub@ in @l@, @-1@ if there are no occurrences.
-- Equivalent to @`offsetIndexOf` l sub 0@.
--
-- >>> prove $ \(l :: SList Int8) i -> i .> 0 .&& i .< length l .=> indexOf l (subList l i 1) .<= i
-- Q.E.D.
-- >>> prove $ \(l :: SList Word16) i -> i .> 0 .&& i .< length l .=> indexOf l (subList l i 1) .== i
-- Falsifiable. Counter-example:
--   s0 = [32,0,0] :: [Word16]
--   s1 =        2 :: Integer
-- >>> prove $ \(l1 :: SList Word16) l2 -> length l2 .> length l1 .=> indexOf l1 l2 .== -1
-- Q.E.D.
indexOf :: SymVal a => SList a -> SList a -> SInteger
indexOf s sub = offsetIndexOf s sub 0

-- | @`offsetIndexOf` l sub offset@. Retrieves first position of @sub@ at or
-- after @offset@ in @l@, @-1@ if there are no occurrences.
--
-- >>> prove $ \(l :: SList Int8) sub -> offsetIndexOf l sub 0 .== indexOf l sub
-- Q.E.D.
-- >>> prove $ \(l :: SList Int8) sub i -> i .>= length l .&& length sub .> 0 .=> offsetIndexOf l sub i .== -1
-- Q.E.D.
-- >>> prove $ \(l :: SList Int8) sub i -> i .> length l .=> offsetIndexOf l sub i .== -1
-- Q.E.D.
offsetIndexOf :: SymVal a => SList a -> SList a -> SInteger -> SInteger
offsetIndexOf s sub offset
  | Just c <- unliteral s        -- a constant list
  , Just n <- unliteral sub      -- a constant search pattern
  , Just o <- unliteral offset   -- at a constant offset
  , o >= 0, o <= genericLength c        -- offset is good
  = case [i | (i, t) <- zip [o ..] (L.tails (genericDrop o c)), n `L.isPrefixOf` t] of
      (i:_) -> literal i
      _     -> -1
  | True
  = lift3 SeqIndexOf Nothing s sub offset

-- | Lift a unary operator over lists.
lift1 :: forall a b. (SymVal a, SymVal b) => SeqOp -> Maybe (a -> b) -> SBV a -> SBV b
lift1 w mbOp a
  | Just cv <- concEval1 mbOp a
  = cv
  | True
  = SBV $ SVal k $ Right $ cache r
  where k = kindOf (Proxy @b)
        r st = do sva <- sbvToSV st a
                  newExpr st k (SBVApp (SeqOp w) [sva])

-- | Lift a binary operator over lists.
lift2 :: forall a b c. (SymVal a, SymVal b, SymVal c) => SeqOp -> Maybe (a -> b -> c) -> SBV a -> SBV b -> SBV c
lift2 w mbOp a b
  | Just cv <- concEval2 mbOp a b
  = cv
  | True
  = SBV $ SVal k $ Right $ cache r
  where k = kindOf (Proxy @c)
        r st = do sva <- sbvToSV st a
                  svb <- sbvToSV st b
                  newExpr st k (SBVApp (SeqOp w) [sva, svb])

-- | Lift a ternary operator over lists.
lift3 :: forall a b c d. (SymVal a, SymVal b, SymVal c, SymVal d) => SeqOp -> Maybe (a -> b -> c -> d) -> SBV a -> SBV b -> SBV c -> SBV d
lift3 w mbOp a b c
  | Just cv <- concEval3 mbOp a b c
  = cv
  | True
  = SBV $ SVal k $ Right $ cache r
  where k = kindOf (Proxy @d)
        r st = do sva <- sbvToSV st a
                  svb <- sbvToSV st b
                  svc <- sbvToSV st c
                  newExpr st k (SBVApp (SeqOp w) [sva, svb, svc])

-- | Concrete evaluation for unary ops
concEval1 :: (SymVal a, SymVal b) => Maybe (a -> b) -> SBV a -> Maybe (SBV b)
concEval1 mbOp a = literal <$> (mbOp <*> unliteral a)

-- | Concrete evaluation for binary ops
concEval2 :: (SymVal a, SymVal b, SymVal c) => Maybe (a -> b -> c) -> SBV a -> SBV b -> Maybe (SBV c)
concEval2 mbOp a b = literal <$> (mbOp <*> unliteral a <*> unliteral b)

-- | Concrete evaluation for ternary ops
concEval3 :: (SymVal a, SymVal b, SymVal c, SymVal d) => Maybe (a -> b -> c -> d) -> SBV a -> SBV b -> SBV c -> Maybe (SBV d)
concEval3 mbOp a b c = literal <$> (mbOp <*> unliteral a <*> unliteral b <*> unliteral c)

-- | Is the list concretely known empty?
isConcretelyEmpty :: SymVal a => SList a -> Bool
isConcretelyEmpty sl | Just l <- unliteral sl = P.null l
                     | True                   = False
