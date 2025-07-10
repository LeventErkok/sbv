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
-- you use the @OverloadedLists@ and @OverloadedStrings@ extensions to allow literal
-- lists and strings to be used as symbolic literals.
--
-- You can find proofs of many list related properties in "Data.SBV.TP.List".
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                    #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE OverloadedLists        #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module Data.SBV.List (
        -- * Length, emptiness
          length, null

        -- * Deconstructing/Reconstructing
        , nil, (.:), snoc, head, tail, uncons, init, last, singleton, listToListAt, elemAt, (!!), implode, concat, (++)

        -- * Containment
        , elem, notElem, isInfixOf, isSuffixOf, isPrefixOf

        -- * List equality
        , listEq

        -- * Sublists
        , take, drop, splitAt, subList, replace, indexOf, offsetIndexOf

        -- * Reverse
        , reverse

        -- * Mapping
        , map, concatMap

        -- * Difference
        , (\\)

        -- * Folding
        , foldl, foldr

        -- * Zipping
        , zip, zipWith

        -- * Lookup
        , lookup

        -- * Filtering
        , filter, partition, takeWhile, dropWhile

        -- * Predicate transformers
        , all, any, and, or

        -- * Generators
        , replicate, inits, tails

        -- * Sum and product
        , sum, product

        -- * Conversion between strings and naturals
        , strToNat, natToStr

        -- * Symbolic enumerations
        , EnumSymbolic(..)
        ) where

import Prelude hiding (head, tail, init, last, length, take, drop, splitAt, concat, null, elem,
                       notElem, reverse, (++), (!!), map, concatMap, foldl, foldr, zip, zipWith, filter,
                       all, any, and, or, replicate, fst, snd, sum, product, Enum(..), lookup,
                       takeWhile, dropWhile)
import qualified Prelude as P

import Data.SBV.Core.Kind
import Data.SBV.Core.Data
import Data.SBV.Core.Model
import Data.SBV.Core.SizedFloats
import Data.SBV.Core.Floating

import Data.SBV.Tuple

import Data.Maybe (isNothing, catMaybes)
import qualified Data.Char as C

import Data.List (genericLength, genericIndex, genericDrop, genericTake, genericReplicate)
import qualified Data.List as L (inits, tails, isSuffixOf, isPrefixOf, isInfixOf, partition, (\\))

import Data.Proxy

import GHC.Exts (IsList(..))

#ifdef DOCTEST
-- $setup
-- >>> import Prelude hiding (head, tail, init, last, length, take, drop, concat, null, elem, notElem, reverse, (++), (!!), map, foldl, foldr, zip, zipWith, filter, all, any, replicate, lookup, splitAt, concatMap, and, or, sum, product, takeWhile, dropWhile)
-- >>> import qualified Prelude as P(map)
-- >>> import Data.SBV
-- >>> :set -XDataKinds
-- >>> :set -XOverloadedLists
-- >>> :set -XOverloadedStrings
-- >>> :set -XScopedTypeVariables
-- >>> :set -XTypeApplications
-- >>> :set -XQuasiQuotes
#endif

-- | IsList instance allows list literals to be written compactly.
instance SymVal a => IsList (SList a) where
  type Item (SList a) = SBV a

  fromList = P.foldr (.:) nil -- Don't use [] here for nil, as this is the very definition of doing overloaded lists
  toList x = case unliteral x of
               Nothing -> error "IsList.toList used in a symbolic context"
               Just xs -> P.map literal xs

-- | Length of a list.
--
-- >>> sat $ \(l :: SList Word16) -> length l .== 2
-- Satisfiable. Model:
--   s0 = [0,0] :: [Word16]
-- >>> sat $ \(l :: SList Word16) -> length l .< 0
-- Unsatisfiable
-- >>> prove $ \(l1 :: SList Word16) (l2 :: SList Word16) -> length l1 + length l2 .== length (l1 ++ l2)
-- Q.E.D.
-- >>> sat $ \(s :: SString) -> length s .== 2
-- Satisfiable. Model:
--   s0 = "BA" :: String
-- >>> sat $ \(s :: SString) -> length s .< 0
-- Unsatisfiable
-- >>> prove $ \(s1 :: SString) s2 -> length s1 + length s2 .== length (s1 ++ s2)
-- Q.E.D.
length :: forall a. SymVal a => SList a -> SInteger
length = lift1 False (SeqLen (kindOf (Proxy @a))) (Just (fromIntegral . P.length))

-- | @`null` s@ is True iff the list is empty
--
-- >>> prove $ \(l :: SList Word16) -> null l .<=> length l .== 0
-- Q.E.D.
-- >>> prove $ \(l :: SList Word16) -> null l .<=> l .== []
-- Q.E.D.
-- >>> prove $ \(s :: SString) -> null s .<=> length s .== 0
-- Q.E.D.
-- >>> prove $ \(s :: SString) -> null s .<=> s .== ""
-- Q.E.D.
null :: SymVal a => SList a -> SBool
null l
  | Just cs <- unliteral l
  = literal (P.null cs)
  | True
  = length l .== 0

-- | @`head`@ returns the first element of a list. Unspecified if the list is empty.
--
-- >>> prove $ \c -> head [c] .== (c :: SInteger)
-- Q.E.D.
-- >>> prove $ \c -> c .== literal 'A' .=> ([c] :: SString) .== "A"
-- Q.E.D.
-- >>> prove $ \(c :: SChar) -> length ([c] :: SString) .== 1
-- Q.E.D.
-- >>> prove $ \(c :: SChar) -> head ([c] :: SString) .== c
-- Q.E.D.
head :: SymVal a => SList a -> SBV a
head = (`elemAt` 0)

-- | @`tail`@ returns the tail of a list. Unspecified if the list is empty.
--
-- >>> prove $ \(h :: SInteger) t -> tail ([h] ++ t) .== t
-- Q.E.D.
-- >>> prove $ \(l :: SList Integer) -> length l .> 0 .=> length (tail l) .== length l - 1
-- Q.E.D.
-- >>> prove $ \(l :: SList Integer) -> sNot (null l) .=> [head l] ++ tail l .== l
-- Q.E.D.
-- >>> prove $ \(h :: SChar) s -> tail ([h] ++ s) .== s
-- Q.E.D.
-- >>> prove $ \(s :: SString) -> length s .> 0 .=> length (tail s) .== length s - 1
-- Q.E.D.
-- >>> prove $ \(s :: SString) -> sNot (null s) .=> [head s] ++ tail s .== s
-- Q.E.D.
tail :: SymVal a => SList a -> SList a
tail l
 | Just (_:cs) <- unliteral l
 = literal cs
 | True
 = subList l 1 (length l - 1)

-- | @`uncons`@ returns the pair of the head and tail. Unspecified if the list is empty.
--
-- >>> prove $ \(x :: SInteger) xs -> uncons (x .: xs) .== (x, xs)
-- Q.E.D.
uncons :: SymVal a => SList a -> (SBV a, SList a)
uncons l = (head l, tail l)

-- | @`init`@ returns all but the last element of the list. Unspecified if the list is empty.
--
-- >>> prove $ \(h :: SInteger) t -> init (t ++ [h]) .== t
-- Q.E.D.
-- >>> prove $ \(c :: SChar) t -> init (t ++ [c]) .== t
-- Q.E.D.
init :: SymVal a => SList a -> SList a
init l
 | Just cs@(_:_) <- unliteral l
 = literal $ P.init cs
 | True
 = subList l 0 (length l - 1)

-- | @`last`@ returns the last element of the list. Unspecified if the list is empty.
--
-- >>> prove $ \(l :: SInteger) i -> last (i ++ [l]) .== l
-- Q.E.D.
last :: SymVal a => SList a -> SBV a
last l = l `elemAt` (length l - 1)

-- | @`singleton` x@ is the list of length 1 that contains the only value @x@.
--
-- >>> prove $ \(x :: SInteger) -> head [x] .== x
-- Q.E.D.
-- >>> prove $ \(x :: SInteger) -> length [x] .== 1
-- Q.E.D.
singleton :: forall a. SymVal a => SBV a -> SList a
singleton = lift1 False (SeqUnit (kindOf (Proxy @a))) (Just (: []))

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
-- >>> prove $ \i -> i .>= 0 .&& i .<= 4 .=> "AAAAA" `elemAt` i .== literal 'A'
-- Q.E.D.
elemAt :: forall a. SymVal a => SList a -> SInteger -> SBV a
elemAt l i
  | Just xs <- unliteral l, Just ci <- unliteral i, ci >= 0, ci < genericLength xs, let x = xs `genericIndex` ci
  = literal x
  | True
  = lift2 False (SeqNth (kindOf (Proxy @a))) Nothing l i

-- | Short cut for 'elemAt'
--
-- >>> prove $ \(xs :: SList Integer) i -> xs !! i .== xs `elemAt` i
-- Q.E.D.
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
-- >>> prove $ \(c1 :: SChar) c2 c3 -> length (implode [c1, c2, c3]) .== 3
-- Q.E.D.
-- >>> prove $ \(c1 :: SChar) c2 c3 -> P.map (elemAt (implode [c1, c2, c3])) (P.map literal [0 .. 2]) .== [c1, c2, c3]
-- Q.E.D.
implode :: SymVal a => [SBV a] -> SList a
implode = P.foldr ((++) . \x -> [x]) (literal [])

-- | Prepend an element, the traditional @cons@.
--
-- >>> 1 .: 2 .: 3 .: [4, 5, 6 :: SInteger]
-- [1,2,3,4,5,6] :: [SInteger]
infixr 5 .:
(.:) :: SymVal a => SBV a -> SList a -> SList a
a .: as = singleton a ++ as  -- NB. Don't do "[a] ++ as" here. That type-checks but is recursive due to how overloaded-lists work.

-- | Append an element
--
-- >>> [1, 2, 3 :: SInteger] `snoc` 4 `snoc` 5 `snoc` 6
-- [1,2,3,4,5,6] :: [SInteger]
snoc :: SymVal a => SList a -> SBV a -> SList a
as `snoc` a = as ++ [a]

-- | Empty list. This value has the property that it's the only list with length 0. If you use @OverloadedLists@ extension,
-- you can write it as the familiar `[]`.
--
-- >>> prove $ \(l :: SList Integer) -> length l .== 0 .<=> l .== []
-- Q.E.D.
-- >>> prove $ \(l :: SString) -> length l .== 0 .<=> l .== []
-- Q.E.D.
nil :: SymVal a => SList a
nil = literal []

-- | Append two lists.
--
-- >>> sat $ \x y (z :: SList Integer) -> length x .== 5 .&& length y .== 1 .&& x ++ y ++ z .== [sEnum|1 .. 12|]
-- Satisfiable. Model:
--   s0 =      [1,2,3,4,5] :: [Integer]
--   s1 =              [6] :: [Integer]
--   s2 = [7,8,9,10,11,12] :: [Integer]
-- >>> sat $ \(x :: SString) y z -> length x .== 5 .&& length y .== 1 .&& x ++ y ++ z .== "Hello world!"
-- Satisfiable. Model:
--   s0 =  "Hello" :: String
--   s1 =      " " :: String
--   s2 = "world!" :: String
infixr 5 ++
(++) :: forall a. SymVal a => SList a -> SList a -> SList a
x ++ y | isConcretelyEmpty x = y
       | isConcretelyEmpty y = x
       | True                = lift2 False (SeqConcat (kindOf (Proxy @a))) (Just (P.++)) x y

-- | @`elem` e l@. Does @l@ contain the element @e@?
--
-- >>> prove $ \(xs :: SList Integer) x -> x `elem` xs .=> length xs .>= 1
-- Q.E.D.
elem :: (Eq a, SymVal a) => SBV a -> SList a -> SBool
e `elem` l = [e] `isInfixOf` l

-- | @`notElem` e l@. Does @l@ not contain the element @e@?
--
-- >>> prove $ \(x :: SList Integer) -> x `notElem` []
-- Q.E.D.
notElem :: (Eq a, SymVal a) => SBV a -> SList a -> SBool
e `notElem` l = sNot (e `elem` l)

-- | @`isInfixOf` sub l@. Does @l@ contain the subsequence @sub@?
--
-- >>> prove $ \(l1 :: SList Integer) l2 l3 -> l2 `isInfixOf` (l1 ++ l2 ++ l3)
-- Q.E.D.
-- >>> prove $ \(l1 :: SList Integer) l2 -> l1 `isInfixOf` l2 .&& l2 `isInfixOf` l1 .<=> l1 .== l2
-- Q.E.D.
-- >>> prove $ \(s1 :: SString) s2 s3 -> s2 `isInfixOf` (s1 ++ s2 ++ s3)
-- Q.E.D.
-- >>> prove $ \(s1 :: SString) s2 -> s1 `isInfixOf` s2 .&& s2 `isInfixOf` s1 .<=> s1 .== s2
-- Q.E.D.
isInfixOf :: forall a. (Eq a, SymVal a) => SList a -> SList a -> SBool
sub `isInfixOf` l
  | isConcretelyEmpty sub
  = literal True
  | True
  = lift2 True (SeqContains (kindOf (Proxy @a))) (Just (flip L.isInfixOf)) l sub -- NB. flip, since `SeqContains` takes args in rev order!

-- | @`isPrefixOf` pre l@. Is @pre@ a prefix of @l@?
--
-- >>> prove $ \(l1 :: SList Integer) l2 -> l1 `isPrefixOf` (l1 ++ l2)
-- Q.E.D.
-- >>> prove $ \(l1 :: SList Integer) l2 -> l1 `isPrefixOf` l2 .=> subList l2 0 (length l1) .== l1
-- Q.E.D.
-- >>> prove $ \(s1 :: SString) s2 -> s1 `isPrefixOf` (s1 ++ s2)
-- Q.E.D.
-- >>> prove $ \(s1 :: SString) s2 -> s1 `isPrefixOf` s2 .=> subList s2 0 (length s1) .== s1
-- Q.E.D.
isPrefixOf :: forall a. (Eq a, SymVal a) => SList a -> SList a -> SBool
pre `isPrefixOf` l
  | isConcretelyEmpty pre
  = literal True
  | True
  = lift2 True (SeqPrefixOf (kindOf (Proxy @a))) (Just L.isPrefixOf) pre l

-- | @listEq@ is a variant of equality that you can use for lists of floats. It respects @NaN /= NaN@. The reason
-- we do not do this automatically is that it complicates proof objectives usually, as it does not simply resolve to
-- the native equality check.
listEq :: forall a. SymVal a => SList a -> SList a -> SBool
listEq
  | containsFloats (kindOf (Proxy @a))
  = smtFunction "listEq" $ \xs ys -> ite (null xs) (null ys) (head xs .== head ys .&& listEq (tail xs) (tail ys))
  | True
  = (.==)

-- | @`isSuffixOf` suf l@. Is @suf@ a suffix of @l@?
--
-- >>> prove $ \(l1 :: SList Word16) l2 -> l2 `isSuffixOf` (l1 ++ l2)
-- Q.E.D.
-- >>> prove $ \(l1 :: SList Word16) l2 -> l1 `isSuffixOf` l2 .=> subList l2 (length l2 - length l1) (length l1) .== l1
-- Q.E.D.
-- >>> prove $ \(s1 :: SString) s2 -> s2 `isSuffixOf` (s1 ++ s2)
-- Q.E.D.
-- >>> prove $ \(s1 :: SString) s2 -> s1 `isSuffixOf` s2 .=> subList s2 (length s2 - length s1) (length s1) .== s1
-- Q.E.D.
isSuffixOf :: forall a. (Eq a, SymVal a) => SList a -> SList a -> SBool
suf `isSuffixOf` l
  | isConcretelyEmpty suf
  = literal True
  | True
  = lift2 True (SeqSuffixOf (kindOf (Proxy @a))) (Just L.isSuffixOf) suf l

-- | @`take` len l@. Corresponds to Haskell's `take` on symbolic lists.
--
-- >>> prove $ \(l :: SList Integer) i -> i .>= 0 .=> length (take i l) .<= i
-- Q.E.D.
-- >>> prove $ \(s :: SString) i -> i .>= 0 .=> length (take i s) .<= i
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
-- >>> prove $ \(s :: SString) i -> length (drop i s) .<= length s
-- Q.E.D.
-- >>> prove $ \(s :: SString) i -> take i s ++ drop i s .== s
-- Q.E.D.
drop :: SymVal a => SInteger -> SList a -> SList a
drop i s = ite (i .>= ls) (literal [])
         $ ite (i .<= 0)  s
         $ subList s i (ls - i)
  where ls = length s

-- | @splitAt n xs = (take n xs, drop n xs)@
--
-- >>> prove $ \n (xs :: SList Integer) -> let (l, r) = splitAt n xs in l ++ r .== xs
-- Q.E.D.
splitAt :: SymVal a => SInteger -> SList a -> (SList a, SList a)
splitAt n xs = (take n xs, drop n xs)

-- | @`subList` s offset len@ is the sublist of @s@ at offset @offset@ with length @len@.
-- This function is under-specified when the offset is outside the range of positions in @s@ or @len@
-- is negative or @offset+len@ exceeds the length of @s@.
--
-- >>> prove $ \(l :: SList Integer) i -> i .>= 0 .&& i .< length l .=> subList l 0 i ++ subList l i (length l - i) .== l
-- Q.E.D.
-- >>> sat  $ \i j -> subList [sEnum|1..5|] i j .== [sEnum|2..4::SInteger|]
-- Satisfiable. Model:
--   s0 = 1 :: Integer
--   s1 = 3 :: Integer
-- >>> sat  $ \i j -> subList [sEnum|1..5|] i j .== [sEnum|6..7::SInteger|]
-- Unsatisfiable
-- >>> prove $ \(s1 :: SString) (s2 :: SString) -> subList (s1 ++ s2) (length s1) 1 .== subList s2 0 1
-- Q.E.D.
-- >>> sat $ \(s :: SString) -> length s .>= 2 .&& subList s 0 1 ./= subList s (length s - 1) 1
-- Satisfiable. Model:
--   s0 = "AB" :: String
-- >>> prove $ \(s :: SString) i -> i .>= 0 .&& i .< length s .=> subList s 0 i ++ subList s i (length s - i) .== s
-- Q.E.D.
-- >>> sat  $ \i j -> subList "hello" i j .== ("ell" :: SString)
-- Satisfiable. Model:
--   s0 = 1 :: Integer
--   s1 = 3 :: Integer
-- >>> sat  $ \i j -> subList "hell" i j .== ("no" :: SString)
-- Unsatisfiable
subList :: forall a. SymVal a => SList a -> SInteger -> SInteger -> SList a
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
  = lift3 False (SeqSubseq (kindOf (Proxy @a))) Nothing l offset len

-- | @`replace` l src dst@. Replace the first occurrence of @src@ by @dst@ in @s@
--
-- >>> prove $ \l -> replace [sEnum|1..5|] l [sEnum|6..10|] .== [sEnum|6..10|] .=> l .== [sEnum|1..5::SWord8|]
-- Q.E.D.
-- >>> prove $ \(l1 :: SList Integer) l2 l3 -> length l2 .> length l1 .=> replace l1 l2 l3 .== l1
-- Q.E.D.
-- >>> prove $ \(s :: SString) -> replace "hello" s "world" .== "world" .=> s .== "hello"
-- Q.E.D.
-- >>> prove $ \(s1 :: SString) s2 s3 -> length s2 .> length s1 .=> replace s1 s2 s3 .== s1
-- Q.E.D.
replace :: forall a. (Eq a, SymVal a) => SList a -> SList a -> SList a -> SList a
replace l src dst
  | Just b <- unliteral src, P.null b   -- If src is null, simply prepend
  = dst ++ l
  | eqCheckIsObjectEq ka
  , Just a <- unliteral l
  , Just b <- unliteral src
  , Just c <- unliteral dst
  = literal $ walk a b c
  | True
  = lift3 True (SeqReplace ka) Nothing l src dst
  where walk haystack needle newNeedle = go haystack   -- note that needle is guaranteed non-empty here.
           where go []       = []
                 go i@(c:cs)
                  | needle `L.isPrefixOf` i = newNeedle P.++ genericDrop (genericLength needle :: Integer) i
                  | True                    = c : go cs

        ka = kindOf (Proxy @a)

-- | @`indexOf` l sub@. Retrieves first position of @sub@ in @l@, @-1@ if there are no occurrences.
-- Equivalent to @`offsetIndexOf` l sub 0@.
--
-- >>> prove $ \(l1 :: SList Word16) l2 -> length l2 .> length l1 .=> indexOf l1 l2 .== -1
-- Q.E.D.
-- >>> prove $ \s1 s2 -> length s2 .> length s1 .=> indexOf s1 s2 .== -1
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
-- >>> prove $ \(s :: SString) sub -> offsetIndexOf s sub 0 .== indexOf s sub
-- Q.E.D.
-- >>> prove $ \(s :: SString) sub i -> i .>= length s .&& length sub .> 0 .=> offsetIndexOf s sub i .== -1
-- Q.E.D.
-- >>> prove $ \(s :: SString) sub i -> i .> length s .=> offsetIndexOf s sub i .== -1
-- Q.E.D.
offsetIndexOf :: forall a. (Eq a, SymVal a) => SList a -> SList a -> SInteger -> SInteger
offsetIndexOf s sub offset
  | eqCheckIsObjectEq ka
  , Just c <- unliteral s        -- a constant list
  , Just n <- unliteral sub      -- a constant search pattern
  , Just o <- unliteral offset   -- at a constant offset
  , o >= 0, o <= genericLength c        -- offset is good
  = case [i | (i, t) <- P.zip [o ..] (L.tails (genericDrop o c)), n `L.isPrefixOf` t] of
      (i:_) -> literal i
      _     -> -1
  | True
  = lift3 True (SeqIndexOf ka) Nothing s sub offset
  where ka = kindOf (Proxy @a)

-- | @`reverse` s@ reverses the sequence.
--
-- NB. We can define @reverse@ in terms of @foldl@ as: @foldl (\soFar elt -> [elt] ++ soFar) []@
-- But in my experiments, I found that this definition performs worse instead of the recursive definition
-- SBV generates for reverse calls. So we're keeping it intact.
--
-- >>> sat $ \(l :: SList Integer) -> reverse l .== literal [3, 2, 1]
-- Satisfiable. Model:
--   s0 = [1,2,3] :: [Integer]
-- >>> prove $ \(l :: SList Word32) -> reverse l .== [] .<=> null l
-- Q.E.D.
-- >>> sat $ \(l :: SString ) -> reverse l .== "321"
-- Satisfiable. Model:
--   s0 = "123" :: String
-- >>> prove $ \(l :: SString) -> reverse l .== "" .<=> null l
-- Q.E.D.
reverse :: forall a. SymVal a => SList a -> SList a
reverse l
  | Just l' <- unliteral l
  = literal (P.reverse l')
  | True
  = def l
  where def = smtFunction "sbv.reverse" $ \xs -> ite (null xs) [] (let (h, t) = uncons xs in def t ++ [h])

-- | A class of mappable functions. In SBV, we make a distinction between closures and regular functions, and
-- we instantiate this class appropriately so it can handle both cases.
class (SymVal a, SymVal b) => SMap func a b | func -> a b where
  -- | Map a function (or a closure) over a symbolic list.
  --
  -- >>> map (+ (1 :: SInteger)) [sEnum|1 .. 5 :: SInteger|]
  -- [2,3,4,5,6] :: [SInteger]
  -- >>> map (+ (1 :: SWord 8)) [sEnum|1 .. 5 :: SWord 8|]
  -- [2,3,4,5,6] :: [SWord8]
  -- >>> map (\x -> [x] :: SList Integer) [sEnum|1 .. 3 :: SInteger|]
  -- [[1],[2],[3]] :: [[SInteger]]
  -- >>> import Data.SBV.Tuple
  -- >>> map (\t -> t^._1 + t^._2) (literal [(x, y) | x <- [1..3], y <- [4..6]] :: SList (Integer, Integer))
  -- [5,6,7,6,7,8,7,8,9] :: [SInteger]
  --
  -- Of course, SBV's 'map' can also be reused in reverse:
  --
  -- >>> sat $ \l -> map (+(1 :: SInteger)) l .== [1,2,3 :: SInteger]
  -- Satisfiable. Model:
  --   s0 = [0,1,2] :: [Integer]
  map :: func -> SList a -> SList b

  -- | Handle the concrete case of mapping. Used internally only.
  concreteMap :: func -> (SBV a -> SBV b) -> SList a -> Maybe [b]
  concreteMap _ f sas
    | Just as <- unliteral sas
    = case P.map (unliteral . f . literal) as of
         bs | P.any isNothing bs -> Nothing
            | True               -> Just (catMaybes bs)
    | True
    = Nothing

-- | Mapping symbolic functions.
instance (SymVal a, SymVal b) => SMap (SBV a -> SBV b) a b where
  -- | @`map` f s@ maps the operation on to sequence.
  map f l
    | Just concResult <- concreteMap f f l
    = literal concResult
    | True
    = sbvMap l
    where sbvMap = smtHOFunction "sbv.map" f $ \xs -> ite (null xs) [] (let (h, t) = uncons xs in f h .: sbvMap t)

-- | Mapping symbolic closures.
instance (SymVal env, SymVal a, SymVal b) => SMap (Closure (SBV env) (SBV a -> SBV b)) a b where
  map cls@Closure{closureEnv, closureFun} l
    | Just concResult <- concreteMap cls (closureFun closureEnv) l
    = literal concResult
    | True
    = sbvMap (tuple (closureEnv, l))
    where sbvMap = smtHOFunction "sbv.closureMap" closureFun
                 $ \envxs -> let (cEnv, xs) = untuple envxs
                                 (h, t)     = uncons xs
                             in ite (null xs) [] (closureFun cEnv h .: sbvMap (tuple (cEnv, t)))

-- | @concatMap f xs@ maps f over elements and concats the result.
--
-- >>> concatMap (\x -> [x, x] :: SList Integer) [sEnum|1 .. 3|]
-- [1,1,2,2,3,3] :: [SInteger]
concatMap :: (SMap func a [b], SymVal b) => func -> SList a -> SList b
concatMap f = concat . map f

-- | A class of left foldable functions. In SBV, we make a distinction between closures and regular functions, and
-- we instantiate this class appropriately so it can handle both cases.
class (SymVal a, SymVal b) => SFoldL func a b | func -> a b where
  -- | @`foldl` f base s@ folds the from the left.
  --
  -- >>> foldl ((+) @SInteger) 0 [sEnum|1 .. 5|]
  -- 15 :: SInteger
  -- >>> foldl ((*) @SInteger) 1 [sEnum|1 .. 5|]
  -- 120 :: SInteger
  -- >>> foldl (\soFar elt -> [elt] ++ soFar) ([] :: SList Integer) [sEnum|1 .. 5|]
  -- [5,4,3,2,1] :: [SInteger]
  --
  -- Again, we can use 'Data.SBV.List.foldl' in the reverse too:
  --
  -- >>> sat $ \l -> foldl (\soFar elt -> [elt] ++ soFar) ([] :: SList Integer) l .== [5, 4, 3, 2, 1 :: SInteger]
  -- Satisfiable. Model:
  --   s0 = [1,2,3,4,5] :: [Integer]
  foldl :: (SymVal a, SymVal b) => func -> SBV b -> SList a -> SBV b

  -- | Handle the concrete case for folding left. Used internally only.
  concreteFoldl :: func -> (SBV b -> SBV a -> SBV b) -> SBV b -> SList a -> Maybe b
  concreteFoldl _ f sb sas
     | Just b <- unliteral sb, Just as <- unliteral sas
     = go b as
     | True
     = Nothing
     where go b []     = Just b
           go b (e:es) = case unliteral (literal b `f` literal e) of
                           Nothing -> Nothing
                           Just b' -> go b' es

-- | Folding left with symbolic functions.
instance (SymVal a, SymVal b) => SFoldL (SBV b -> SBV a -> SBV b) a b where
  -- | @`foldl` f b s@ folds the sequence from the left.
  foldl f base l
    | Just concResult <- concreteFoldl f f base l
    = literal concResult
    | True
    = sbvFoldl $ tuple (base, l)
    where sbvFoldl = smtHOFunction "sbv.foldl" (uncurry f . untuple)
                   $ \exs -> let (e, xs) = untuple exs
                                 (h, t)  = uncons xs
                             in ite (null xs)
                                    e
                                    (sbvFoldl (tuple (e `f` h, t)))

-- | Folding left with symbolic closures.
instance (SymVal env, SymVal a, SymVal b) => SFoldL (Closure (SBV env) (SBV b -> SBV a -> SBV b)) a b where
  foldl cls@Closure{closureEnv, closureFun} base l
    | Just concResult <- concreteFoldl cls (closureFun closureEnv) base l
    = literal concResult
    | True
    = sbvFoldl $ tuple (closureEnv, base, l)
    where sbvFoldl = smtHOFunction "sbv.closureFoldl" closureFun
                   $ \envxs -> let (cEnv, e, xs) = untuple envxs
                                   (h, t)        = uncons xs
                               in ite (null xs)
                                      e
                                      (sbvFoldl (tuple (cEnv, closureFun closureEnv e h, t)))

-- | A class of right foldable functions. In SBV, we make a distinction between closures and regular functions, and
-- we instantiate this class appropriately so it can handle both cases.
class (SymVal a, SymVal b) => SFoldR func a b | func -> a b where
  -- | @`foldr` f base s@ folds the from the right.
  --
  -- >>> foldr ((+) @SInteger) 0 [sEnum|1 .. 5|]
  -- 15 :: SInteger
  -- >>> foldr ((*) @SInteger) 1 [sEnum|1 .. 5|]
  -- 120 :: SInteger
  -- >>> foldr (\elt soFar -> soFar ++ [elt]) ([] :: SList Integer) [sEnum|1 .. 5|]
  -- [5,4,3,2,1] :: [SInteger]
  foldr :: func -> SBV b -> SList a -> SBV b

  -- | Handle the concrete case for folding left. Used internally only.
  concreteFoldr :: func -> (SBV a -> SBV b -> SBV b) -> SBV b -> SList a -> Maybe b
  concreteFoldr _ f sb sas
     | Just b <- unliteral sb, Just as <- unliteral sas
     = go b as
     | True
     = Nothing
     where go b []     = Just b
           go b (e:es) = case go b es of
                           Nothing  -> Nothing
                           Just res -> unliteral (literal e `f` literal res)

-- | Folding right with symbolic functions.
instance (SymVal a, SymVal b) => SFoldR (SBV a -> SBV b -> SBV b) a b where
  -- | @`foldr` f base s@ folds the sequence from the right.
  foldr f base l
    | Just concResult <- concreteFoldr f f base l
    = literal concResult
    | True
    = sbvFoldr $ tuple (base, l)
    where sbvFoldr = smtHOFunction "sbv.foldr" (uncurry f . untuple)
                   $ \exs -> let (e, xs) = untuple exs
                                 (h, t)  = uncons xs
                             in ite (null xs)
                                    e
                                    (h `f` sbvFoldr (tuple (e, t)))

-- | Folding right with symbolic closures.
instance (SymVal env, SymVal a, SymVal b) => SFoldR (Closure (SBV env) (SBV a -> SBV b -> SBV b)) a b where
  foldr cls@Closure{closureEnv, closureFun} base l
    | Just concResult <- concreteFoldr cls (closureFun closureEnv) base l
    = literal concResult
    | True
    = sbvFoldr $ tuple (closureEnv, base, l)
    where sbvFoldr = smtHOFunction "sbv.closureFoldr" closureFun
                   $ \envxs -> let (cEnv, e, xs) = untuple envxs
                                   (h, t)        = uncons xs
                               in ite (null xs)
                                      e
                                      (closureFun closureEnv h (sbvFoldr (tuple (cEnv, e, t))))

-- | @`zip` xs ys@ zips the lists to give a list of pairs. The length of the final list is
-- the minumum of the lengths of the given lists.
--
-- >>> zip [sEnum|1..10 :: SInteger|] [sEnum|11..20 :: SInteger|]
-- [(1,11),(2,12),(3,13),(4,14),(5,15),(6,16),(7,17),(8,18),(9,19),(10,20)] :: [(SInteger, SInteger)]
-- >>> import Data.SBV.Tuple
-- >>> foldr ((+) @SInteger) 0 (map (\t -> t^._1+t^._2::SInteger) (zip [sEnum|1..10|] [sEnum|10, 9..1|]))
-- 110 :: SInteger
zip :: forall a b. (SymVal a, SymVal b) => SList a -> SList b -> SList (a, b)
zip xs ys
 | Just xs' <- unliteral xs, Just ys' <- unliteral ys
 = literal $ P.zip xs' ys'
 | True
 = def xs ys
 where def = smtFunction "sbv.zip" $ \as bs -> ite (null as .|| null bs) [] (tuple (head as, head bs) .: def (tail as) (tail bs))

-- | A class of function that we can zip-with. In SBV, we make a distinction between closures and regular
-- functions, and we instantiate this class appropriately so it can handle both cases.
class (SymVal a, SymVal b, SymVal c) => SZipWith func a b c | func -> a b c where
  -- | @`zipWith` f xs ys@ zips the lists to give a list of pairs, applying the function to each pair of elements.
  -- The length of the final list is the minumum of the lengths of the given lists.
   --
   -- >>> zipWith ((+) @SInteger) ([sEnum|1..10::SInteger|]) ([sEnum|11..20::SInteger|])
   -- [12,14,16,18,20,22,24,26,28,30] :: [SInteger]
   -- >>> foldr ((+) @SInteger) 0 (zipWith ((+) @SInteger) [sEnum|1..10 :: SInteger|] [sEnum|10, 9..1 :: SInteger|])
   -- 110 :: SInteger
  zipWith :: func -> SList a -> SList b -> SList c

  -- | Handle the concrete case of zipping. Used internally only.
  concreteZipWith :: func -> (SBV a -> SBV b -> SBV c) -> SList a -> SList b -> Maybe [c]
  concreteZipWith _ f sas sbs
   | Just as <- unliteral sas, Just bs <- unliteral sbs
   = go as bs
   | True
   = Nothing
   where go []     _      = Just []
         go _      []     = Just []
         go (a:as) (b:bs) = (:) <$> unliteral (literal a `f` literal b) <*> go as bs

-- | Zipping with symbolic functions.
instance (SymVal a, SymVal b, SymVal c) => SZipWith (SBV a -> SBV b -> SBV c) a b c where
   -- | @`zipWith`@ zips two sequences with a symbolic function.
   zipWith f xs ys
    | Just concResult <- concreteZipWith f f xs ys
    = literal concResult
    | True
    = sbvZipWith $ tuple (xs, ys)
    where sbvZipWith = smtHOFunction "sbv.zipWith" (uncurry f . untuple)
                     $ \asbs -> let (as, bs) = untuple asbs
                                in ite (null as .|| null bs)
                                       []
                                       (f (head as) (head bs) .: sbvZipWith (tuple (tail as, tail bs)))

-- | Zipping with closures.
instance (SymVal env, SymVal a, SymVal b, SymVal c) => SZipWith (Closure (SBV env) (SBV a -> SBV b -> SBV c)) a b c where
   zipWith cls@Closure{closureEnv, closureFun} xs ys
    | Just concResult <- concreteZipWith cls (closureFun closureEnv) xs ys
    = literal concResult
    | True
    = sbvZipWith $ tuple (closureEnv, xs, ys)
    where sbvZipWith = smtHOFunction "sbv.closureZipWith" closureFun
                     $ \envasbs -> let (cEnv, as, bs) = untuple envasbs
                                   in ite (null as .|| null bs)
                                          []
                                          (closureFun cEnv (head as) (head bs) .: sbvZipWith (tuple (cEnv, tail as, tail bs)))

-- | Concatenate list of lists.
--
-- >>> concat [[sEnum|1..3::SInteger|], [sEnum|4..7|], [sEnum|8..10|]]
-- [1,2,3,4,5,6,7,8,9,10] :: [SInteger]
concat :: forall a. SymVal a => SList [a] -> SList a
concat = foldr (++) []

-- | Check all elements satisfy the predicate.
--
-- >>> let isEven x = x `sMod` 2 .== 0
-- >>> all isEven [2, 4, 6, 8, 10 :: SInteger]
-- True
-- >>> all isEven [2, 4, 6, 1, 8, 10 :: SInteger]
-- False
all :: forall a. SymVal a => (SBV a -> SBool) -> SList a -> SBool
all f = foldr ((.&&) . f) sTrue

-- | Check some element satisfies the predicate.
--
-- >>> let isEven x = x `sMod` 2 .== 0
-- >>> any (sNot . isEven) [2, 4, 6, 8, 10 :: SInteger]
-- False
-- >>> any isEven [2, 4, 6, 1, 8, 10 :: SInteger]
-- True
any :: forall a. SymVal a => (SBV a -> SBool) -> SList a -> SBool
any f = foldr ((.||) . f) sFalse

-- | Conjunction of all the elements.
--
-- >>> and []
-- True
-- >>> prove $ \s -> and [s, sNot s] .== sFalse
-- Q.E.D.
and :: SList Bool -> SBool
and = all id

-- | Disjunction of all the elements.
--
-- >>> or []
-- False
-- >>> prove $ \s -> or [s, sNot s]
-- Q.E.D.
or :: SList Bool -> SBool
or = any id

-- | Replicate an element a given number of times.
--
-- >>> replicate 3 (2 :: SInteger) .== [2, 2, 2 :: SInteger]
-- True
-- >>> replicate (-2) (2 :: SInteger) .== ([] :: SList Integer)
-- True
replicate :: forall a. SymVal a => SInteger -> SBV a -> SList a
replicate c e
 | Just c' <- unliteral c, Just e' <- unliteral e
 = literal (genericReplicate c' e')
 | True
 = def c e
 where def = smtFunction "sbv.replicate" $ \count elt -> ite (count .<= 0) [] (elt .: def (count - 1) elt)

-- | inits of a list.
--
-- >>> inits ([] :: SList Integer)
-- [[]] :: [[SInteger]]
-- >>> inits [1,2,3,4::SInteger]
-- [[],[1],[1,2],[1,2,3],[1,2,3,4]] :: [[SInteger]]
inits :: forall a. SymVal a => SList a -> SList [a]
inits xs
 | Just xs' <- unliteral xs
 = literal (L.inits xs')
 | True
 = def xs
 where def = smtFunction "sbv.inits" $ \l -> ite (null l) [[]] (def (init l) ++ [l])

-- | tails of a list.
--
-- >>> tails ([] :: SList Integer)
-- [[]] :: [[SInteger]]
-- >>> tails [1,2,3,4::SInteger]
-- [[1,2,3,4],[2,3,4],[3,4],[4],[]] :: [[SInteger]]
tails :: forall a. SymVal a => SList a -> SList [a]
tails xs
 | Just xs' <- unliteral xs
 = literal (L.tails xs')
 | True
 = def xs
 where def = smtFunction "sbv.tails" $ \l -> ite (null l) [[]] (l .: def (tail l))

-- | Difference.
--
-- >>> [1, 2] \\ [3, 4 :: SInteger]
-- [1,2] :: [SInteger]
-- >>> [1, 2] \\ [2, 4 :: SInteger]
-- [1] :: [SInteger]
(\\) :: forall a. (Eq a, SymVal a) => SList a -> SList a -> SList a
xs \\ ys
 | Just xs' <- unliteral xs, Just ys' <- unliteral ys
 = literal (xs' L.\\ ys')
 | True
 = def xs ys
 where def = smtFunction "sbv.diff" $ \x y -> ite (null x)
                                                  []
                                                  (let (h, t) = uncons x
                                                       r      = def t y
                                                   in ite (h `elem` y) r (h .: r))
infix 5 \\  -- CPP: do not eat the final newline

-- | A class of filtering-like functions. In SBV, we make a distinction between closures and regular functions,
-- and we instantiate this class appropriately so it can handle both cases.
class SymVal a => SFilter func a | func -> a where
  -- | Filter a list via a predicate.
  --
  -- >>> filter (\(x :: SInteger) -> x `sMod` 2 .== 0) (literal [1 .. 10])
  -- [2,4,6,8,10] :: [SInteger]
  -- >>> filter (\(x :: SInteger) -> x `sMod` 2 ./= 0) (literal [1 .. 10])
  -- [1,3,5,7,9] :: [SInteger]
  filter :: func -> SList a -> SList a

  -- | Handle the concrete case of filtering. Used internally only.
  concreteFilter :: func -> (SBV a -> SBool) -> SList a -> Maybe [a]
  concreteFilter _ f sas
   | Just as <- unliteral sas
   = case P.map (unliteral . f . literal) as of
        xs | P.any isNothing xs -> Nothing
           | True               -> Just [e | (True, e) <- P.zip (catMaybes xs) as]
   | True
   = Nothing

  -- | Partition a symbolic list according to a predicate.
  --
  -- >>> partition (\(x :: SInteger) -> x `sMod` 2 .== 0) (literal [1 .. 10])
  -- ([2,4,6,8,10],[1,3,5,7,9]) :: ([SInteger], [SInteger])
  partition :: func -> SList a -> STuple [a] [a]

  -- | Handle the concrete case of partitioning. Used internally only.
  concretePartition :: func -> (SBV a -> SBool) -> SList a -> Maybe ([a], [a])
  concretePartition _ f l
    | Just l' <- unliteral l
    = case P.map (unliteral . f . literal) l' of
        xs | P.any isNothing xs -> Nothing
           | True               -> let (ts, fs) = L.partition P.fst (P.zip (catMaybes xs) l')
                                   in Just (P.map P.snd ts, P.map P.snd fs)
    | True
    = Nothing

  -- | Symbolic equivalent of @takeWhile@
  --
  -- >>> takeWhile (\(x :: SInteger) -> x `sMod` 2 .== 0) (literal [1..10])
  -- [] :: [SInteger]
  -- >>> takeWhile (\(x :: SInteger) -> x `sMod` 2 ./= 0) (literal [1..10])
  -- [1] :: [SInteger]
  takeWhile :: func -> SList a -> SList a

  -- | Handle the concrete case of take-while. Used internally only.
  concreteTakeWhile :: func -> (SBV a -> SBool) -> SList a -> Maybe [a]
  concreteTakeWhile _ f sas
   | Just as <- unliteral sas
   = case P.map (unliteral . f . literal) as of
        xs | P.any isNothing xs -> Nothing
           | True               -> Just (P.map P.snd (P.takeWhile P.fst (P.zip (catMaybes xs) as)))
   | True
   = Nothing

  -- | Symbolic equivalent of @dropWhile@
  -- >>> dropWhile (\(x :: SInteger) -> x `sMod` 2 .== 0) (literal [1..10])
  -- [1,2,3,4,5,6,7,8,9,10] :: [SInteger]
  -- >>> dropWhile (\(x :: SInteger) -> x `sMod` 2 ./= 0) (literal [1..10])
  -- [2,3,4,5,6,7,8,9,10] :: [SInteger]
  dropWhile :: func -> SList a -> SList a

  -- | Handle the concrete case of take-while. Used internally only.
  concreteDropWhile :: func -> (SBV a -> SBool) -> SList a -> Maybe [a]
  concreteDropWhile _ f sas
   | Just as <- unliteral sas
   = case P.map (unliteral . f . literal) as of
        xs | P.any isNothing xs -> Nothing
           | True               -> Just (P.map P.snd (P.dropWhile P.fst (P.zip (catMaybes xs) as)))
   | True
   = Nothing

-- | Filtering with symbolic functions.
instance SymVal a => SFilter (SBV a -> SBool) a where
  -- | @filter f xs@ filters the list with the given predicate.
  filter f l
    | Just concResult <- concreteFilter f f l
    = literal concResult
    | True
    = sbvFilter l
    where sbvFilter = smtHOFunction "sbv.filter" f $ \xs -> ite (null xs)
                                                                []
                                                                (let (h, t) = uncons xs
                                                                     r      = sbvFilter t
                                                                 in ite (f h) (h .: r) r)

  -- | @partition f xs@ splits the list into two and returns those that satisfy the predicate in the
  -- first element, and those that don't in the second.
  partition f l
    | Just concResult <- concretePartition f f l
    = literal concResult
    | True
    = sbvPartition l
    where sbvPartition = smtHOFunction "sbv.partition" f $ \xs -> ite (null xs)
                                                                      (tuple ([], []))
                                                                      (let (h, t)   = uncons xs
                                                                           (as, bs) = untuple $ sbvPartition t
                                                                       in ite (f h)
                                                                              (tuple (h .: as, bs))
                                                                              (tuple (as, h .: bs)))

  -- | @takeWhile f xs@ takes the prefix of @xs@ that satisfy the predicate.
  takeWhile f l
    | Just concResult <- concreteTakeWhile f f l
    = literal concResult
    | True
    = sbvTakeWhile l
    where sbvTakeWhile = smtHOFunction "sbv.takeWhile" f $ \xs -> ite (null xs)
                                                                      []
                                                                      (let (h, t) = uncons xs
                                                                       in ite (f h) (h .: sbvTakeWhile t) [])

  -- | @dropWhile f xs@ drops the prefix of @xs@ that satisfy the predicate.
  dropWhile f l
    | Just concResult <- concreteDropWhile f f l
    = literal concResult
    | True
    = sbvDropWhile l
    where sbvDropWhile = smtHOFunction "sbv.dropWhile" f $ \xs -> ite (null xs)
                                                                      []
                                                                      (let (h, t) = uncons xs
                                                                       in ite (f h) (sbvDropWhile t) xs)

-- | Filtering with closures.
instance (SymVal env, SymVal a) => SFilter (Closure (SBV env) (SBV a -> SBool)) a where
  filter cls@Closure{closureEnv, closureFun} l
    | Just concResult <- concreteFilter cls (closureFun closureEnv) l
    = literal concResult
    | True
    = sbvFilter (tuple (closureEnv, l))
    where sbvFilter = smtHOFunction "sbv.closureFilter" closureFun
                    $ \envxs -> let (cEnv, xs) = untuple envxs
                                    (h, t)     = uncons xs
                                    r          = sbvFilter (tuple (cEnv, t))
                                in ite (closureFun cEnv h) (h .: r) r

  partition cls@Closure{closureEnv, closureFun} l
    | Just concResult <- concretePartition cls (closureFun closureEnv) l
    = literal concResult
    | True
    = sbvPartition (tuple (closureEnv, l))
    where sbvPartition = smtHOFunction "sbv.closurePartition" closureFun
                       $ \envxs -> let (cEnv, xs) = untuple envxs
                                       (h,    t)  = uncons xs
                                       (as,   bs) = untuple $ sbvPartition (tuple (cEnv, t))
                                   in ite (closureFun cEnv h)
                                          (tuple (h .: as, bs))
                                          (tuple (as, h .: bs))

  takeWhile cls@Closure{closureEnv, closureFun} l
    | Just concResult <- concreteTakeWhile cls (closureFun closureEnv) l
    = literal concResult
    | True
    = sbvTakeWhile (tuple (closureEnv, l))
    where sbvTakeWhile = smtHOFunction "sbv.closureTakeWhile" closureFun
                       $ \envxs -> let (cEnv, xs) = untuple envxs
                                       (h, t)     = uncons xs
                                in ite (closureFun cEnv h) (h .: sbvTakeWhile (tuple (cEnv, t))) []

  dropWhile cls@Closure{closureEnv, closureFun} l
    | Just concResult <- concreteDropWhile cls (closureFun closureEnv) l
    = literal concResult
    | True
    = sbvDropWhile (tuple (closureEnv, l))
    where sbvDropWhile = smtHOFunction "sbv.closureDropWhile" closureFun
                       $ \envxs -> let (cEnv, xs) = untuple envxs
                                       (h, t)     = uncons xs
                                in ite (closureFun cEnv h) (sbvDropWhile (tuple (cEnv, t))) xs

-- | @`sum` s@. Sum the given sequence.
--
-- >>> sum [sEnum|1 .. 10::SInteger|]
-- 55 :: SInteger
sum :: forall a. (SymVal a, Num (SBV a)) => SList a -> SBV a
sum = foldr ((+) @(SBV a)) 0

-- | @`product` s@. Multiply out the given sequence.
--
-- >>> product [sEnum|1 .. 10::SInteger|]
-- 3628800 :: SInteger
product :: forall a. (SymVal a, Num (SBV a)) => SList a -> SBV a
product = foldr ((*) @(SBV a)) 1

-- | A class of symbolic aware enumerations. This is similar to Haskell's @Enum@ class,
-- except some of the methods are generalized to work with symbolic values. Together
-- with the 'Data.SBV.sEnum' quasiquoter, you can write symbolic arithmetic progressions,
-- such as:
--
-- >>> [sEnum| 5, 7 .. 16::SInteger|]
-- [5,7,9,11,13,15] :: [SInteger]
-- >>> [sEnum| 4 ..|] :: SList (WordN 4)
-- [4,5,6,7,8,9,10,11,12,13,14,15] :: [SWord 4]
-- >>> [sEnum| 9, 12 ..|] :: SList (IntN 4)
-- [-7,-4,-1,2,5] :: [SInt 4]
class EnumSymbolic a where
   -- | @`succ`@, same as in the @Enum@ class
   succ :: SBV a -> SBV a

   -- | @`pred`@, same as in the @Enum@ class
   pred :: SBV a -> SBV a

   -- | @`toEnum`@, same as in the @Enum@ class, except it takes an 'SInteger'
   toEnum :: SInteger -> SBV a

   -- | @`fromEnum`@, same as in the @Enum@ class, except it returns an 'SInteger'
   fromEnum :: SBV a -> SInteger

   -- | @`enumFrom` m@. Symbolic version of @[m ..]@
   enumFrom :: SBV a -> SList a

   -- | @`enumFromThen` m@. Symbolic version of @[m, m' ..]@
   enumFromThen :: SBV a -> SBV a -> SList a

   -- | @`enumFromTo` m n@. Symbolic version of @[m .. n]@
   enumFromTo :: SymVal a => SBV a -> SBV a -> SList a

   -- | @`enumFromThenTo` m n@. Symbolic version of @[m, m' .. n]@
   enumFromThenTo :: SymVal a => SBV a -> SBV a -> SBV a -> SList a

-- | 'EnumSymbolic' instance for words
instance {-# OVERLAPPABLE #-} (SymVal a, Bounded a, Integral a, Num a, Num (SBV a)) => EnumSymbolic a where
  succ = smtFunction "EnumSymbolic.succ" (\x -> ite (x .== maxBound) (some "EnumSymbolic.succ.maxBound" (const sTrue)) (x+1))
  pred = smtFunction "EnumSymbolic.pred" (\x -> ite (x .== minBound) (some "EnumSymbolic.pred.minBound" (const sTrue)) (x-1))

  toEnum = smtFunction "EnumSymbolic.toEnum" $ \x ->
                         ite (x .< sFromIntegral (minBound @(SBV a))) (some "EnumSymbolic.toEnum.<minBound" (const sTrue))
                       $ ite (x .> sFromIntegral (maxBound @(SBV a))) (some "EnumSymbolic.toEnum.>maxBound" (const sTrue))
                       $ sFromIntegral x

  fromEnum = sFromIntegral

  enumFrom n   = map sFromIntegral (enumFromTo @Integer (sFromIntegral n) (sFromIntegral (maxBound @(SBV a))))
  enumFromThen = smtFunction "EnumSymbolic.enumFromThen" $ \n1 n2 ->
                             let i_n1, i_n2 :: SInteger
                                 i_n1 = sFromIntegral n1
                                 i_n2 = sFromIntegral n2
                             in map sFromIntegral (ite (i_n2 .>= i_n1)
                                                       (enumFromThenTo i_n1 i_n2 (sFromIntegral (maxBound @(SBV a))))
                                                       (enumFromThenTo i_n1 i_n2 (sFromIntegral (minBound @(SBV a)))))

  enumFromTo     n m   = map sFromIntegral (enumFromTo     @Integer (sFromIntegral n) (sFromIntegral m))
  enumFromThenTo n m t = map sFromIntegral (enumFromThenTo @Integer (sFromIntegral n) (sFromIntegral m) (sFromIntegral t))

-- | 'EnumSymbolic' instance for integer. NB. The above definition goes thru integers, hence we need to define this explicitly.
instance {-# OVERLAPPING #-} EnumSymbolic Integer where
   succ x = x + 1
   pred x = x - 1

   toEnum   = id
   fromEnum = id

   enumFrom   n = enumFromThen   n (n+1)
   enumFromTo n = enumFromThenTo n (n+1)

   enumFromThen x y = go x (y-x)
     where go = smtFunction "EnumSymbolic.Integer.enumFromThen" $ \start delta -> start .: go (start+delta) delta

   enumFromThenTo x y z = ite (delta .>= 0) (up x delta z) (down x delta z)
     where delta = y - x

           up, down :: SInteger -> SInteger -> SInteger -> SList Integer
           up    = smtFunction "EnumSymbolic.Integer.enumFromThenTo.up"   $ \start d end -> ite (start .> end) [] (start .: up   (start + d) d end)
           down  = smtFunction "EnumSymbolic.Integer.enumFromThenTo.down" $ \start d end -> ite (start .< end) [] (start .: down (start + d) d end)

-- | 'EnumSymbolic instance for 'Float'. Note that the termination requirement as defined by the Haskell standard for floats state:
--      > For Float and Double, the semantics of the enumFrom family is given by the rules for Int above,
--      > except that the list terminates when the elements become greater than @e3 + i/2@ for positive increment @i@,
--      > or when they become less than @e3 + i/2@ for negative @i@.
instance {-# OVERLAPPING #-} EnumSymbolic Float where
   succ x = x + 1
   pred x = x - 1

   toEnum   = sFromIntegral
   fromEnum = fromSFloat sRTZ

   enumFrom   n = enumFromThen   n (n+1)
   enumFromTo n = enumFromThenTo n (n+1)

   enumFromThen x y = go 0 x (y-x)
     where go = smtFunction "EnumSymbolic.Float.enumFromThen" $ \k n d -> (n + k * d) .: go (k+1) n d

   enumFromThenTo x y zIn = ite (delta .>= 0) (up 0 x delta z) (down 0 x delta z)
     where delta, z :: SFloat
           delta = y - x
           z     = zIn + delta / 2

           up, down :: SFloat -> SFloat -> SFloat -> SFloat -> SList Float
           up    = smtFunction "EnumSymbolic.Float.enumFromThenTo.up"   $ \k n d end -> let c = n + k * d in ite (c .> end) [] (c .: up   (k+1) n d end)
           down  = smtFunction "EnumSymbolic.Float.enumFromThenTo.down" $ \k n d end -> let c = n + k * d in ite (c .< end) [] (c .: down (k+1) n d end)

-- | 'EnumSymbolic instance for 'Double'
instance {-# OVERLAPPING #-} EnumSymbolic Double where
   succ x = x + 1
   pred x = x - 1

   toEnum   = sFromIntegral
   fromEnum = fromSDouble sRTZ

   enumFrom   n = enumFromThen   n (n+1)
   enumFromTo n = enumFromThenTo n (n+1)

   enumFromThen x y = go 0 x (y-x)
     where go = smtFunction "EnumSymbolic.Double.enumFromThen" $ \k n d -> (n + k * d) .: go (k+1) n d

   enumFromThenTo x y zIn = ite (delta .>= 0) (up 0 x delta z) (down 0 x delta z)
     where delta, z :: SDouble
           delta = y - x
           z     = zIn + delta / 2

           up, down :: SDouble -> SDouble -> SDouble -> SDouble -> SList Double
           up    = smtFunction "EnumSymbolic.Double.enumFromThenTo.up"   $ \k n d end -> let c = n + k * d in ite (c .> end) [] (c .: up   (k+1) n d end)
           down  = smtFunction "EnumSymbolic.Double.enumFromThenTo.down" $ \k n d end -> let c = n + k * d in ite (c .< end) [] (c .: down (k+1) n d end)

-- | 'EnumSymbolic instance for arbitrary floats
instance {-# OVERLAPPING #-} ValidFloat eb sb => EnumSymbolic (FloatingPoint eb sb) where
   succ x = x + 1
   pred x = x - 1

   toEnum   = sFromIntegral
   fromEnum = fromSFloatingPoint sRTZ

   enumFrom   n = enumFromThen   n (n+1)
   enumFromTo n = enumFromThenTo n (n+1)

   enumFromThen x y = go 0 x (y-x)
     where go = smtFunction "EnumSymbolic.FloatingPoint.enumFromThen" $ \k n d -> (n + k * d) .: go (k+1) n d

   enumFromThenTo x y zIn = ite (delta .>= 0) (up 0 x delta z) (down 0 x delta z)
     where delta, z :: SFloatingPoint eb sb
           delta = y - x
           z     = zIn + delta / 2

           up, down :: SFloatingPoint eb sb -> SFloatingPoint eb sb -> SFloatingPoint eb sb -> SFloatingPoint eb sb -> SList (FloatingPoint eb sb)
           up    = smtFunction "EnumSymbolic.FloatingPoint.enumFromThenTo.up"   $ \k n d end -> let c = n + k * d in ite (c .> end) [] (c .: up   (k+1) n d end)
           down  = smtFunction "EnumSymbolic.FloatingPoint.enumFromThenTo.down" $ \k n d end -> let c = n + k * d in ite (c .< end) [] (c .: down (k+1) n d end)

-- | 'EnumSymbolic instance for arbitrary AlgReal. We don't have to use the multiplicative trick here
-- since alg-reals are precise. But, following rational in Haskell, we do use the stopping point of @z + delta / 2@.
instance {-# OVERLAPPING #-} EnumSymbolic AlgReal where
   succ x = x + 1
   pred x = x - 1

   toEnum   = sFromIntegral
   fromEnum = sRealToSIntegerTruncate

   enumFrom   n = enumFromThen   n (n+1)
   enumFromTo n = enumFromThenTo n (n+1)

   enumFromThen x y = go x (y-x)
     where go = smtFunction "EnumSymbolic.AlgReal.enumFromThen" $ \start delta -> start .: go (start+delta) delta

   enumFromThenTo x y zIn = ite (delta .>= 0) (up x delta z) (down x delta z)
     where delta, z :: SReal
           delta = y - x
           z     = zIn + delta / 2

           up, down :: SReal -> SReal -> SReal -> SList AlgReal
           up    = smtFunction "EnumSymbolic.AlgReal.enumFromThenTo.up"   $ \start d end -> ite (start .> end) [] (start .: up   (start + d) d end)
           down  = smtFunction "EnumSymbolic.AlgReal.enumFromThenTo.down" $ \start d end -> ite (start .< end) [] (start .: down (start + d) d end)

-- | Lookup. If we can't find, then the result is unspecified.
--
-- >>> lookup (4 :: SInteger) (literal [(5, 12), (4, 3), (2, 6 :: Integer)])
-- 3 :: SInteger
-- >>> prove  $ \(x :: SInteger) -> x .== lookup 9 (literal [(5, 12), (4, 3), (2, 6 :: Integer)])
-- Falsifiable. Counter-example:
--   Data.SBV.List.lookup_notFound @Integer = 0 :: Integer
--   s0                                     = 1 :: Integer
lookup :: (SymVal k, SymVal v) => SBV k -> SList (k, v) -> SBV v
lookup = smtFunction "Data.SBV.List.lookup" $ \k lst -> ite (null lst)
                                                            (some "Data.SBV.List.lookup_notFound" (const sTrue))
                                                            (let (k', v) = untuple (head lst)
                                                             in ite (k .== k') v (lookup k (tail lst)))

-- | @`strToNat` s@. Retrieve integer encoded by string @s@ (ground rewriting only).
-- Note that by definition this function only works when @s@ only contains digits,
-- that is, if it encodes a natural number. Otherwise, it returns '-1'.
--
-- >>> prove $ \s -> let n = strToNat s in length s .== 1 .=> (-1) .<= n .&& n .<= 9
-- Q.E.D.
strToNat :: SString -> SInteger
strToNat s
 | Just a <- unliteral s
 = if P.all C.isDigit a && not (P.null a)
   then literal (read a)
   else -1
 | True
 = lift1Str StrStrToNat Nothing s

-- | @`natToStr` i@. Retrieve string encoded by integer @i@ (ground rewriting only).
-- Again, only naturals are supported, any input that is not a natural number
-- produces empty string, even though we take an integer as an argument.
--
-- >>> prove $ \i -> length (natToStr i) .== 3 .=> i .<= 999
-- Q.E.D.
natToStr :: SInteger -> SString
natToStr i
 | Just v <- unliteral i
 = literal $ if v >= 0 then show v else ""
 | True
 = lift1Str StrNatToStr Nothing i

-- | Lift a unary operator over lists.
lift1 :: forall a b. (SymVal a, SymVal b) => Bool -> SeqOp -> Maybe (a -> b) -> SBV a -> SBV b
lift1 simpleEq w mbOp a
  | Just cv <- concEval1 simpleEq mbOp a
  = cv
  | True
  = SBV $ SVal k $ Right $ cache r
  where k = kindOf (Proxy @b)
        r st = do sva <- sbvToSV st a
                  newExpr st k (SBVApp (SeqOp w) [sva])

-- | Lift a binary operator over lists.
lift2 :: forall a b c. (SymVal a, SymVal b, SymVal c) => Bool -> SeqOp -> Maybe (a -> b -> c) -> SBV a -> SBV b -> SBV c
lift2 simpleEq w mbOp a b
  | Just cv <- concEval2 simpleEq mbOp a b
  = cv
  | True
  = SBV $ SVal k $ Right $ cache r
  where k = kindOf (Proxy @c)
        r st = do sva <- sbvToSV st a
                  svb <- sbvToSV st b
                  newExpr st k (SBVApp (SeqOp w) [sva, svb])

-- | Lift a ternary operator over lists.
lift3 :: forall a b c d. (SymVal a, SymVal b, SymVal c, SymVal d) => Bool -> SeqOp -> Maybe (a -> b -> c -> d) -> SBV a -> SBV b -> SBV c -> SBV d
lift3 simpleEq w mbOp a b c
  | Just cv <- concEval3 simpleEq mbOp a b c
  = cv
  | True
  = SBV $ SVal k $ Right $ cache r
  where k = kindOf (Proxy @d)
        r st = do sva <- sbvToSV st a
                  svb <- sbvToSV st b
                  svc <- sbvToSV st c
                  newExpr st k (SBVApp (SeqOp w) [sva, svb, svc])

-- | Concrete evaluation for unary ops
concEval1 :: forall a b. (SymVal a, SymVal b) => Bool -> Maybe (a -> b) -> SBV a -> Maybe (SBV b)
concEval1 simpleEq mbOp a
  | not simpleEq || eqCheckIsObjectEq (kindOf (Proxy @a)) = literal <$> (mbOp <*> unliteral a)
  | True                                                  = Nothing

-- | Concrete evaluation for binary ops
concEval2 :: forall a b c. (SymVal a, SymVal b, SymVal c) => Bool -> Maybe (a -> b -> c) -> SBV a -> SBV b -> Maybe (SBV c)
concEval2 simpleEq mbOp a b
  | not simpleEq || eqCheckIsObjectEq (kindOf (Proxy @a)) = literal <$> (mbOp <*> unliteral a <*> unliteral b)
  | True                                                  = Nothing

-- | Concrete evaluation for ternary ops
concEval3 :: forall a b c d. (SymVal a, SymVal b, SymVal c, SymVal d) => Bool -> Maybe (a -> b -> c -> d) -> SBV a -> SBV b -> SBV c -> Maybe (SBV d)
concEval3 simpleEq mbOp a b c
  | not simpleEq || eqCheckIsObjectEq (kindOf (Proxy @a)) = literal <$> (mbOp <*> unliteral a <*> unliteral b <*> unliteral c)
  | True                                                  = Nothing

-- | Is the list concretely known empty?
isConcretelyEmpty :: SymVal a => SList a -> Bool
isConcretelyEmpty sl | Just l <- unliteral sl = P.null l
                     | True                   = False

-- | Lift a unary operator over strings.
lift1Str :: forall a b. (SymVal a, SymVal b) => StrOp -> Maybe (a -> b) -> SBV a -> SBV b
lift1Str w mbOp a
  | Just cv <- literal <$> (mbOp <*> unliteral a)
  = cv
  | True
  = SBV $ SVal k $ Right $ cache r
  where k = kindOf (Proxy @b)
        r st = do sva <- sbvToSV st a
                  newExpr st k (SBVApp (StrOp w) [sva])

{- HLint ignore implode "Use :" -}
