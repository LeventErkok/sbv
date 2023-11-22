-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.List
-- Copyright : (c) Joel Burget
--                 Levent Erkok
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

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.List (
        -- * Length, emptiness
          length, null
        -- * Deconstructing/Reconstructing
        , head, tail, uncons, init, singleton, listToListAt, elemAt, (!!), implode, concat, (.:), snoc, nil, (++)
        -- * Containment
        , elem, notElem, isInfixOf, isSuffixOf, isPrefixOf
        -- * Sublists
        , take, drop, subList, replace, indexOf, offsetIndexOf
        -- * Reverse
        , reverse
        -- * Mapping
        , map, mapi
        -- * Folding
        , foldl, foldr, foldli, foldri
        -- * Zipping
        , zip, zipWith
        -- * Filtering
        , filter
        -- * Other list functions
        , all, any
        ) where

import Prelude hiding (head, tail, init, length, take, drop, concat, null, elem,
                       notElem, reverse, (++), (!!), map, foldl, foldr, zip, zipWith, filter, all, any)
import qualified Prelude as P

import Data.SBV.Core.Data hiding (StrOp(..))
import Data.SBV.Core.Model

import Data.SBV.Lambda
import Data.SBV.Tuple

import Data.Maybe (isNothing, catMaybes)

import Data.List (genericLength, genericIndex, genericDrop, genericTake)
import qualified Data.List as L (tails, isSuffixOf, isPrefixOf, isInfixOf)

import Data.Proxy

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Prelude hiding (head, tail, init, length, take, drop, concat, null, elem, notElem, reverse, (++), (!!), map, foldl, foldr, zip, zipWith, filter, all, any)
-- >>> import qualified Prelude as P(map)
-- >>> import Data.SBV
-- >>> :set -XDataKinds
-- >>> :set -XOverloadedLists
-- >>> :set -XScopedTypeVariables

-- | Length of a list.
--
-- >>> sat $ \(l :: SList Word16) -> length l .== 2
-- Satisfiable. Model:
--   s0 = [0,0] :: [Word16]
-- >>> sat $ \(l :: SList Word16) -> length l .< 0
-- Unsatisfiable
-- >>> prove $ \(l1 :: SList Word16) (l2 :: SList Word16) -> length l1 + length l2 .== length (l1 ++ l2)
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
  = length l .== 0

-- | @`head`@ returns the first element of a list. Unspecified if the list is empty.
--
-- >>> prove $ \c -> head (singleton c) .== (c :: SInteger)
-- Q.E.D.
head :: SymVal a => SList a -> SBV a
head = (`elemAt` 0)

-- | @`tail`@ returns the tail of a list. Unspecified if the list is empty.
--
-- >>> prove $ \(h :: SInteger) t -> tail (singleton h ++ t) .== t
-- Q.E.D.
-- >>> prove $ \(l :: SList Integer) -> length l .> 0 .=> length (tail l) .== length l - 1
-- Q.E.D.
-- >>> prove $ \(l :: SList Integer) -> sNot (null l) .=> singleton (head l) ++ tail l .== l
-- Q.E.D.
tail :: SymVal a => SList a -> SList a
tail l
 | Just (_:cs) <- unliteral l
 = literal cs
 | True
 = subList l 1 (length l - 1)

-- | @`uncons`@ returns the pair of the head and tail. Unspecified if the list is empty.
uncons :: SymVal a => SList a -> (SBV a, SList a)
uncons l = (head l, tail l)

-- | @`init`@ returns all but the last element of the list. Unspecified if the list is empty.
--
-- >>> prove $ \(h :: SInteger) t -> init (t ++ singleton h) .== t
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
-- >>> prove $ \(l1 :: SList Integer) l2 -> listToListAt (l1 ++ l2) (length l1) .== listToListAt l2 0
-- Q.E.D.
-- >>> sat $ \(l :: SList Word16) -> length l .>= 2 .&& listToListAt l 0 ./= listToListAt l (length l - 1)
-- Satisfiable. Model:
--   s0 = [0,64] :: [Word16]
listToListAt :: SymVal a => SList a -> SInteger -> SList a
listToListAt s offset = subList s offset 1

-- | @`elemAt` l i@ is the value stored at location @i@, starting at 0. Unspecified if
-- index is out of bounds.
--
-- >>> prove $ \i -> i `inRange` (0, 4) .=> [1,1,1,1,1] `elemAt` i .== (1::SInteger)
-- Q.E.D.
elemAt :: SymVal a => SList a -> SInteger -> SBV a
elemAt l i
  | Just xs <- unliteral l, Just ci <- unliteral i, ci >= 0, ci < genericLength xs, let x = xs `genericIndex` ci
  = literal x
  | True
  = lift2 SeqNth Nothing l i

-- | Short cut for 'elemAt'
(!!) :: SymVal a => SList a -> SInteger -> SBV a
(!!) = elemAt

-- | @`implode` es@ is the list of length @|es|@ containing precisely those
-- elements. Note that there is no corresponding function @explode@, since
-- we wouldn't know the length of a symbolic list.
--
-- >>> prove $ \(e1 :: SInteger) e2 e3 -> length (implode [e1, e2, e3]) .== 3
-- Q.E.D.
-- >>> prove $ \(e1 :: SInteger) e2 e3 -> P.map (elemAt (implode [e1, e2, e3])) (P.map literal [0 .. 2]) .== [e1, e2, e3]
-- Q.E.D.
implode :: SymVal a => [SBV a] -> SList a
implode = P.foldr ((++) . singleton) (literal [])

-- | Prepend an element, the traditional @cons@.
infixr 5 .:
(.:) :: SymVal a => SBV a -> SList a -> SList a
a .: as = singleton a ++ as

-- | Append an element
snoc :: SymVal a => SList a -> SBV a -> SList a
as `snoc` a = as ++ singleton a

-- | Empty list. This value has the property that it's the only list with length 0:
--
-- >>> prove $ \(l :: SList Integer) -> length l .== 0 .<=> l .== nil
-- Q.E.D.
nil :: SymVal a => SList a
nil = []

-- | Append two lists.
--
-- >>> sat $ \x y z -> length x .== 5 .&& length y .== 1 .&& x ++ y ++ z .== [1 .. 12]
-- Satisfiable. Model:
--   s0 =      [1,2,3,4,5] :: [Integer]
--   s1 =              [6] :: [Integer]
--   s2 = [7,8,9,10,11,12] :: [Integer]
infixr 5 ++
(++) :: SymVal a => SList a -> SList a -> SList a
x ++ y | isConcretelyEmpty x = y
       | isConcretelyEmpty y = x
       | True                = lift2 SeqConcat (Just (P.++)) x y

-- | @`elem` e l@. Does @l@ contain the element @e@?
elem :: (Eq a, SymVal a) => SBV a -> SList a -> SBool
e `elem` l = singleton e `isInfixOf` l

-- | @`notElem` e l@. Does @l@ not contain the element @e@?
notElem :: (Eq a, SymVal a) => SBV a -> SList a -> SBool
e `notElem` l = sNot (e `elem` l)

-- | @`isInfixOf` sub l@. Does @l@ contain the subsequence @sub@?
--
-- >>> prove $ \(l1 :: SList Integer) l2 l3 -> l2 `isInfixOf` (l1 ++ l2 ++ l3)
-- Q.E.D.
-- >>> prove $ \(l1 :: SList Integer) l2 -> l1 `isInfixOf` l2 .&& l2 `isInfixOf` l1 .<=> l1 .== l2
-- Q.E.D.
isInfixOf :: (Eq a, SymVal a) => SList a -> SList a -> SBool
sub `isInfixOf` l
  | isConcretelyEmpty sub
  = literal True
  | True
  = lift2 SeqContains (Just (flip L.isInfixOf)) l sub -- NB. flip, since `SeqContains` takes args in rev order!

-- | @`isPrefixOf` pre l@. Is @pre@ a prefix of @l@?
--
-- >>> prove $ \(l1 :: SList Integer) l2 -> l1 `isPrefixOf` (l1 ++ l2)
-- Q.E.D.
-- >>> prove $ \(l1 :: SList Integer) l2 -> l1 `isPrefixOf` l2 .=> subList l2 0 (length l1) .== l1
-- Q.E.D.
isPrefixOf :: (Eq a, SymVal a) => SList a -> SList a -> SBool
pre `isPrefixOf` l
  | isConcretelyEmpty pre
  = literal True
  | True
  = lift2 SeqPrefixOf (Just L.isPrefixOf) pre l

-- | @`isSuffixOf` suf l@. Is @suf@ a suffix of @l@?
--
-- >>> prove $ \(l1 :: SList Word16) l2 -> l2 `isSuffixOf` (l1 ++ l2)
-- Q.E.D.
-- >>> prove $ \(l1 :: SList Word16) l2 -> l1 `isSuffixOf` l2 .=> subList l2 (length l2 - length l1) (length l1) .== l1
-- Q.E.D.
isSuffixOf :: (Eq a, SymVal a) => SList a -> SList a -> SBool
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
-- >>> prove $ \(l :: SList Word16) i -> take i l ++ drop i l .== l
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
-- >>> prove $ \(l :: SList Integer) i -> i .>= 0 .&& i .< length l .=> subList l 0 i ++ subList l i (length l - i) .== l
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
replace :: (Eq a, SymVal a) => SList a -> SList a -> SList a -> SList a
replace l src dst
  | Just b <- unliteral src, P.null b   -- If src is null, simply prepend
  = dst ++ l
  | Just a <- unliteral l
  , Just b <- unliteral src
  , Just c <- unliteral dst
  = literal $ walk a b c
  | True
  = lift3 SeqReplace Nothing l src dst
  where walk haystack needle newNeedle = go haystack   -- note that needle is guaranteed non-empty here.
           where go []       = []
                 go i@(c:cs)
                  | needle `L.isPrefixOf` i = newNeedle P.++ genericDrop (genericLength needle :: Integer) i
                  | True                    = c : go cs

-- | @`indexOf` l sub@. Retrieves first position of @sub@ in @l@, @-1@ if there are no occurrences.
-- Equivalent to @`offsetIndexOf` l sub 0@.
--
-- >>> prove $ \(l1 :: SList Word16) l2 -> length l2 .> length l1 .=> indexOf l1 l2 .== -1
-- Q.E.D.
indexOf :: (Eq a, SymVal a) => SList a -> SList a -> SInteger
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
offsetIndexOf :: (Eq a, SymVal a) => SList a -> SList a -> SInteger -> SInteger
offsetIndexOf s sub offset
  | Just c <- unliteral s        -- a constant list
  , Just n <- unliteral sub      -- a constant search pattern
  , Just o <- unliteral offset   -- at a constant offset
  , o >= 0, o <= genericLength c        -- offset is good
  = case [i | (i, t) <- P.zip [o ..] (L.tails (genericDrop o c)), n `L.isPrefixOf` t] of
      (i:_) -> literal i
      _     -> -1
  | True
  = lift3 SeqIndexOf Nothing s sub offset

-- | @`reverse` s@ reverses the sequence.
--
-- NB. We can define @reverse@ in terms of @foldl@ as: @foldl (\soFar elt -> singleton elt ++ soFar) []@
-- But in my experiments, I found that this definition performs worse instead of the recursive definition
-- SBV generates for reverse calls. So we're keeping it intact.
--
-- >>> sat $ \(l :: SList Integer) -> reverse l .== literal [3, 2, 1]
-- Satisfiable. Model:
--   s0 = [1,2,3] :: [Integer]
-- >>> prove $ \(l :: SList Word32) -> reverse l .== [] .<=> null l
-- Q.E.D.
reverse :: SymVal a => SList a -> SList a
reverse l
  | Just l' <- unliteral l
  = literal (P.reverse l')
  | True
  = SBV $ SVal k $ Right $ cache r
  where k = kindOf l
        r st = do sva <- sbvToSV st l
                  newExpr st k (SBVApp (SeqOp (SBVReverse k)) [sva])

-- | @`map` op s@ maps the operation on to sequence.
--
-- >>> map (+1) [1 .. 5 :: Integer]
-- [2,3,4,5,6] :: [SInteger]
-- >>> map (+1) [1 .. 5 :: WordN 8]
-- [2,3,4,5,6] :: [SWord8]
-- >>> map singleton [1 .. 3 :: Integer]
-- [[1],[2],[3]] :: [[SInteger]]
-- >>> import Data.SBV.Tuple
-- >>> import GHC.Exts (fromList)
-- >>> map (\t -> t^._1 + t^._2) (fromList [(x, y) | x <- [1..3], y <- [4..6]] :: SList (Integer, Integer))
-- [5,6,7,6,7,8,7,8,9] :: [SInteger]
--
-- Of course, SBV's 'map' can also be reused in reverse:
--
-- >>> sat $ \l -> map (+1) l .== [1,2,3 :: Integer]
-- Satisfiable. Model:
--   s0 = [0,1,2] :: [Integer]
map :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b) -> SList a -> SList b
map op l
  | Just l' <- unliteral l, Just concResult <- concreteMap l'
  = literal concResult
  | True
  = SBV $ SVal k $ Right $ cache r
  where concreteMap l' = case P.map (unliteral . op . literal) l' of
                           xs | P.any isNothing xs -> Nothing
                              | True               -> Just (catMaybes xs)

        k = kindOf (Proxy @(SList b))
        r st = do sva <- sbvToSV st l
                  lam <- lambdaStr st (kindOf (Proxy @b)) op
                  newExpr st k (SBVApp (SeqOp (SeqMap lam)) [sva])

-- | @`mapi` op s@ maps the operation on to sequence, with the counter given at each element, starting
-- at the given value. In Haskell terms, it is:
--
-- @
--    mapi :: (Integer -> a -> b) -> Integer -> [a] -> [b]
--    mapi f i xs = zipWith f [i..] xs
-- @
--
-- Note that `mapi` is definable in terms of `Data.SBV.List.zipWith`, with extra coding. The reason why SBV provides
-- this function natively is because it maps to a native function in the underlying solver. So, hopefully it'll perform
-- better in terms being decidable.
--
-- >>> mapi (+) 10 [1 .. 5 :: Integer]
-- [11,13,15,17,19] :: [SInteger]
mapi :: forall a b. (SymVal a, SymVal b) => (SInteger -> SBV a -> SBV b) -> SInteger -> SList a -> SList b
mapi op i l
  | Just l' <- unliteral l, Just i' <- unliteral i, Just concResult <- concMapi i' l'
  = literal concResult
  | True
  = SBV $ SVal k $ Right $ cache r
  where concMapi b xs = case P.zipWith (\o e -> unliteral (op (literal o) (literal e))) [b ..] xs of
                          vs | P.any isNothing vs -> Nothing
                             | True               -> Just (catMaybes vs)

        k = kindOf (Proxy @(SList b))
        r st = do svi <- sbvToSV st i
                  svl <- sbvToSV st l
                  lam <- lambdaStr st (kindOf (Proxy @b)) op
                  newExpr st k (SBVApp (SeqOp (SeqMapI lam)) [svi, svl])

-- | @`foldl` op base s@ folds the from the left.
--
-- >>> foldl (+) 0 [1 .. 5 :: Integer]
-- 15 :: SInteger
-- >>> foldl (*) 1 [1 .. 5 :: Integer]
-- 120 :: SInteger
-- >>> foldl (\soFar elt -> singleton elt ++ soFar) ([] :: SList Integer) [1 .. 5 :: Integer]
-- [5,4,3,2,1] :: [SInteger]
--
-- Again, we can use 'Data.SBV.List.foldl' in the reverse too:
--
-- >>> sat $ \l -> foldl (\soFar elt -> singleton elt ++ soFar) ([] :: SList Integer) l .== [5, 4, 3, 2, 1 :: Integer]
-- Satisfiable. Model:
--   s0 = [1,2,3,4,5] :: [Integer]
foldl :: (SymVal a, SymVal b) => (SBV b -> SBV a -> SBV b) -> SBV b -> SList a -> SBV b
foldl op base l
  | Just l' <- unliteral l, Just base' <- unliteral base, Just concResult <- concreteFoldl base' l'
  = literal concResult
  | True
  = SBV $ SVal k $ Right $ cache r
  where concreteFoldl b []     = Just b
        concreteFoldl b (e:es) = case unliteral (op (literal b) (literal e)) of
                                   Nothing -> Nothing
                                   Just b' -> concreteFoldl b' es

        k = kindOf base
        r st = do svb <- sbvToSV st base
                  svl <- sbvToSV st l
                  lam <- lambdaStr st k op
                  newExpr st k (SBVApp (SeqOp (SeqFoldLeft lam)) [svb, svl])

-- | @`foldli` op i base s@ folds the sequence, with the counter given at each element, starting
-- at the given value. In Haskell terms, it is:
--
-- @
--   foldli :: (Integer -> b -> a -> b) -> Integer -> b -> [a] -> b
--   foldli f c e xs = foldl (\b (i, a) -> f i b a) e (zip [c..] xs)
-- @
--
-- While this function is rather odd looking, it maps directly to the implementation in the underlying solver,
-- and proofs involving it might have better decidability.
--
-- >>> foldli (\i b a -> i+b+a) 10 0 [1 .. 5 :: Integer]
-- 75 :: SInteger
foldli :: (SymVal a, SymVal b) => (SInteger -> SBV b -> SBV a -> SBV b) -> SInteger -> SBV b -> SList a -> SBV b
foldli op baseI baseE l
   | Just l' <- unliteral l, Just baseI' <- unliteral baseI, Just baseE' <- unliteral baseE, Just concResult <- concreteFoldli baseI' baseE' l'
   = literal concResult
   | True
   = SBV $ SVal k $ Right $ cache r
  where concreteFoldli _ b []     = Just b
        concreteFoldli c b (e:es) = case unliteral (op (literal c) (literal b) (literal e)) of
                                      Nothing -> Nothing
                                      Just b' -> concreteFoldli (c+1) b' es

        k = kindOf baseE
        r st = do svi <- sbvToSV st baseI
                  sve <- sbvToSV st baseE
                  sva <- sbvToSV st l
                  lam <- lambdaStr st k op
                  newExpr st k (SBVApp (SeqOp (SeqFoldLeftI lam)) [svi, sve, sva])

-- | @`foldr` op base s@ folds the sequence from the right.
--
-- >>> foldr (+) 0 [1 .. 5 :: Integer]
-- 15 :: SInteger
-- >>> foldr (*) 1 [1 .. 5 :: Integer]
-- 120 :: SInteger
-- >>> foldr (\elt soFar -> soFar ++ singleton elt) ([] :: SList Integer) [1 .. 5 :: Integer]
-- [5,4,3,2,1] :: [SInteger]
foldr :: (SymVal a, SymVal b) => (SBV a -> SBV b -> SBV b) -> SBV b -> SList a -> SBV b
foldr op b = foldl (flip op) b . reverse

-- | @`foldri` op base i s@ folds the sequence from the right, with the counter given at each element, starting
-- at the given value. This function is provided as a parallel to `foldli`.
foldri :: (SymVal a, SymVal b) => (SBV a -> SBV b -> SInteger -> SBV b) -> SBV b -> SInteger -> SList a -> SBV b
foldri op baseE baseI = foldli (\a b i -> op i b a) baseI baseE . reverse

-- | @`zip` xs ys@ zips the lists to give a list of pairs. The length of the final list is
-- the minumum of the lengths of the given lists.
--
-- >>> zip [1..10::Integer] [11..20::Integer]
-- [(1,11),(2,12),(3,13),(4,14),(5,15),(6,16),(7,17),(8,18),(9,19),(10,20)] :: [(SInteger, SInteger)]
-- >>> import Data.SBV.Tuple
-- >>> foldr (+) 0 (map (\t -> t^._1+t^._2::SInteger) (zip [1..10::Integer] [10, 9..1::Integer]))
-- 110 :: SInteger
zip :: (SymVal a, SymVal b) => SList a -> SList b -> SList (a, b)
zip xs ys = map (\t -> tuple (t^._2, ys `elemAt` (t^._1)))
                (mapi (curry tuple) 0 (take (length ys) xs))

-- | @`zipWith` f xs ys@ zips the lists to give a list of pairs, applying the function to each pair of elements.
-- The length of the final list is the minumum of the lengths of the given lists.
--
-- >>> zipWith (+) [1..10::Integer] [11..20::Integer]
-- [12,14,16,18,20,22,24,26,28,30] :: [SInteger]
-- >>> foldr (+) 0 (zipWith (+) [1..10::Integer] [10, 9..1::Integer])
-- 110 :: SInteger
zipWith :: (SymVal a, SymVal b, SymVal c) => (SBV a -> SBV b -> SBV c) -> SList a -> SList b -> SList c
zipWith f xs ys = map (\t -> f (t^._2) (ys `elemAt` (t^._1)))
                      (mapi (curry tuple) 0 (take (length ys) xs))

-- | Concatenate list of lists.
--
-- NB. Concat is typically defined in terms of foldr. Here we prefer foldl, since the underlying solver
-- primitive is foldl: Otherwise, we'd induce an extra call to reverse.
--
-- >>> concat [[1..3::Integer], [4..7], [8..10]]
-- [1,2,3,4,5,6,7,8,9,10] :: [SInteger]
concat :: SymVal a => SList [a] -> SList a
concat = foldl (++) []

-- | Check all elements satisfy the predicate.
--
-- >>> let isEven x = x `sMod` 2 .== 0
-- >>> all isEven [2, 4, 6, 8, 10 :: Integer]
-- True
-- >>> all isEven [2, 4, 6, 1, 8, 10 :: Integer]
-- False
all :: SymVal a => (SBV a -> SBool) -> SList a -> SBool
all f = foldl (\sofar e -> sofar .&& f e) sTrue

-- | Check some element satisfies the predicate.
-- --
-- >>> let isEven x = x `sMod` 2 .== 0
-- >>> any (sNot . isEven) [2, 4, 6, 8, 10 :: Integer]
-- False
-- >>> any isEven [2, 4, 6, 1, 8, 10 :: Integer]
-- True
any :: SymVal a => (SBV a -> SBool) -> SList a -> SBool
any f = foldl (\sofar e -> sofar .|| f e) sFalse

-- | @filter f xs@ filters the list with the given predicate.
--
-- >>> filter (\x -> x `sMod` 2 .== 0) [1 .. 10 :: Integer]
-- [2,4,6,8,10] :: [SInteger]
-- >>> filter (\x -> x `sMod` 2 ./= 0) [1 .. 10 :: Integer]
-- [1,3,5,7,9] :: [SInteger]
filter :: SymVal a => (SBV a -> SBool) -> SList a -> SList a
filter f = foldl (\sofar e -> sofar ++ ite (f e) (singleton e) []) []

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
