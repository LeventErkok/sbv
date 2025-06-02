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
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.List (
        -- * Length, emptiness
          length, null
        -- * Deconstructing/Reconstructing
        , head, tail, uncons, init, last, singleton, listToListAt, elemAt, (!!), implode, concat, (.:), snoc, nil, (++)
        -- * Containment
        , elem, notElem, isInfixOf, isSuffixOf, isPrefixOf
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
        -- * Filtering
        , filter, partition
        -- * Other list functions
        , all, any, and, or, replicate
        -- * Conversion between strings and naturals
        , strToNat, natToStr
        ) where

import Prelude hiding (head, tail, init, last, length, take, drop, splitAt, concat, null, elem,
                       notElem, reverse, (++), (!!), map, concatMap, foldl, foldr, zip, zipWith, filter,
                       all, any, and, or, replicate)
import qualified Prelude as P

import Data.SBV.Core.Kind
import Data.SBV.Core.Data
import Data.SBV.Core.Model

import Data.SBV.Lambda

import Data.SBV.Tuple hiding (fst, snd)

import Data.Maybe (isNothing, catMaybes)
import qualified Data.Char as C

import Data.List (genericLength, genericIndex, genericDrop, genericTake, genericReplicate)
import qualified Data.List as L (tails, isSuffixOf, isPrefixOf, isInfixOf, partition, (\\))

import Data.Proxy
import Data.SBV.Utils.Lib (atProxy)

#ifdef DOCTEST
-- $setup
-- >>> import Prelude hiding (head, tail, init, last, length, take, drop, concat, null, elem, notElem, reverse, (++), (!!), map, foldl, foldr, zip, zipWith, filter, all, any, replicate)
-- >>> import qualified Prelude as P(map)
-- >>> import Data.SBV
-- >>> :set -XDataKinds
-- >>> :set -XOverloadedLists
-- >>> :set -XOverloadedStrings
-- >>> :set -XScopedTypeVariables
#endif

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
-- >>> prove $ \c -> head (singleton c) .== (c :: SInteger)
-- Q.E.D.
-- >>> prove $ \c -> c .== literal 'A' .=> singleton c .== "A"
-- Q.E.D.
-- >>> prove $ \(c :: SChar) -> length (singleton c) .== 1
-- Q.E.D.
-- >>> prove $ \(c :: SChar) -> head (singleton c) .== c
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
-- >>> prove $ \(h :: SChar) s -> tail (singleton h ++ s) .== s
-- Q.E.D.
-- >>> prove $ \(s :: SString) -> length s .> 0 .=> length (tail s) .== length s - 1
-- Q.E.D.
-- >>> prove $ \(s :: SString) -> sNot (null s) .=> singleton (head s) ++ tail s .== s
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
-- >>> prove $ \(c :: SChar) t -> init (t ++ singleton c) .== t
-- Q.E.D.
init :: SymVal a => SList a -> SList a
init l
 | Just cs@(_:_) <- unliteral l
 = literal $ P.init cs
 | True
 = subList l 0 (length l - 1)

-- | @`last`@ returns the last element of the list. Unspecified if the list is empty.
--
-- >>> prove $ \(l :: SInteger) i -> last (i ++ singleton l) .== l
-- Q.E.D.
last :: SymVal a => SList a -> SBV a
last l = l `elemAt` (length l - 1)

-- | @`singleton` x@ is the list of length 1 that contains the only value @x@.
--
-- >>> prove $ \(x :: SInteger) -> head (singleton x) .== x
-- Q.E.D.
-- >>> prove $ \(x :: SInteger) -> length (singleton x) .== 1
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
-- >>> prove $ \(l :: SString) -> length l .== 0 .<=> l .== nil
-- Q.E.D.
nil :: SymVal a => SList a
nil = literal []

-- | Append two lists.
--
-- >>> sat $ \x y z -> length x .== 5 .&& length y .== 1 .&& x ++ y ++ z .== [1 .. 12]
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
splitAt :: SymVal a => SInteger -> SList a -> (SList a, SList a)
splitAt n xs = (take n xs, drop n xs)

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
-- >>> prove $ \l -> replace [1..5] l [6..10] .== [6..10] .=> l .== ([1..5] :: SList Word8)
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
-- NB. We can define @reverse@ in terms of @foldl@ as: @foldl (\soFar elt -> singleton elt ++ soFar) []@
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
  where def = smtFunction (atProxy (Proxy @a) "sbv.reverse") $
                          \xs -> ite (null xs) nil (let (h, t) = uncons xs in def t ++ singleton h)

-- | @`map` f s@ maps the operation on to sequence.
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
map f l
  | Just l' <- unliteral l, Just concResult <- concreteMap l'
  = literal concResult
  | True
  = SBV $ SVal (kindOf (Proxy @(SList b)))
        $ firstify (sbvMap, atProxy (Proxy @(a, b)) "sbv.map") (f, kindOf (Proxy @b))
  where concreteMap l' = case P.map (unliteral . f . literal) l' of
                           xs | P.any isNothing xs -> Nothing
                              | True               -> Just (catMaybes xs)

        sbvMap uniq = def l
         where def = smtFunction uniq $ \xs -> ite (null xs) nil (let (h, t) = uncons xs in f h .: def t)

-- | @concatMap f xs@ maps f over elements and concats the result.
concatMap :: (SymVal a, SymVal b) => (SBV a -> SList b) -> SList a -> SList b
concatMap f = concat . map f

-- | @`foldl` f base s@ folds the from the left.
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
foldl :: forall a b. (SymVal a, SymVal b) => (SBV b -> SBV a -> SBV b) -> SBV b -> SList a -> SBV b
foldl f base l
  | Just l' <- unliteral l, Just base' <- unliteral base, Just concResult <- concreteFoldl base' l'
  = literal concResult
  | True
  = SBV $ SVal (kindOf (Proxy @b)) $ firstify (sbvFoldl, atProxy (Proxy @(a, b)) "sbv.foldl") (f, kindOf (Proxy @b))
  where concreteFoldl b []     = Just b
        concreteFoldl b (e:es) = case unliteral (literal b `f` literal e) of
                                   Nothing -> Nothing
                                   Just b' -> concreteFoldl b' es

        sbvFoldl uniq = def base l
          where def = smtFunction uniq $ \e xs -> ite (null xs) e (let (h, t) = uncons xs in def (e `f` h) t)

-- | @`foldr` f base s@ folds the sequence from the right.
--
-- >>> foldr (+) 0 [1 .. 5 :: Integer]
-- 15 :: SInteger
-- >>> foldr (*) 1 [1 .. 5 :: Integer]
-- 120 :: SInteger
-- >>> foldr (\elt soFar -> soFar ++ singleton elt) ([] :: SList Integer) [1 .. 5 :: Integer]
-- [5,4,3,2,1] :: [SInteger]
foldr :: forall a b. (SymVal a, SymVal b) => (SBV a -> SBV b -> SBV b) -> SBV b -> SList a -> SBV b
foldr f base l
  | Just l' <- unliteral l, Just base' <- unliteral base, Just concResult <- concreteFoldr base' l'
  = literal concResult
  | True
  = SBV $ SVal (kindOf (Proxy @b)) $ firstify (sbvFoldr, atProxy (Proxy @(a, b)) "sbv.foldr") (f, kindOf (Proxy @b))
  where concreteFoldr b []     = Just b
        concreteFoldr b (e:es) = case concreteFoldr b es of
                                   Nothing  -> Nothing
                                   Just res -> unliteral (literal e `f` literal res)

        sbvFoldr uniq = def base l
          where def = smtFunction uniq $ \e xs -> ite (null xs) e (let (h, t) = uncons xs in h `f` def e t)

-- | @`zip` xs ys@ zips the lists to give a list of pairs. The length of the final list is
-- the minumum of the lengths of the given lists.
--
-- >>> zip [1..10::Integer] [11..20::Integer]
-- [(1,11),(2,12),(3,13),(4,14),(5,15),(6,16),(7,17),(8,18),(9,19),(10,20)] :: [(SInteger, SInteger)]
-- >>> import Data.SBV.Tuple
-- >>> foldr (+) 0 (map (\t -> t^._1+t^._2::SInteger) (zip [1..10::Integer] [10, 9..1::Integer]))
-- 110 :: SInteger
zip :: forall a b. (SymVal a, SymVal b) => SList a -> SList b -> SList (a, b)
zip xs ys
 | Just xs' <- unliteral xs, Just ys' <- unliteral ys
 = literal $ P.zip xs' ys'
 | True
 = def xs ys
 where def = smtFunction (atProxy (Proxy @(a, b)) "sbv.zip") $
                         \as bs -> ite (null as .|| null bs) nil (tuple (head as, head bs) .: def (tail as) (tail bs))

-- | @`zipWith` f xs ys@ zips the lists to give a list of pairs, applying the function to each pair of elements.
-- The length of the final list is the minumum of the lengths of the given lists.
--
-- >>> zipWith (+) [1..10::Integer] [11..20::Integer]
-- [12,14,16,18,20,22,24,26,28,30] :: [SInteger]
-- >>> foldr (+) 0 (zipWith (+) [1..10::Integer] [10, 9..1::Integer])
-- 110 :: SInteger
zipWith :: forall a b c. (SymVal a, SymVal b, SymVal c) => (SBV a -> SBV b -> SBV c) -> SList a -> SList b -> SList c
zipWith f xs ys
 | Just xs' <- unliteral xs, Just ys' <- unliteral ys, Just concResult <- concreteZipWith xs' ys'
 = literal concResult
 | True
 = SBV $ SVal (kindOf (Proxy @(SList c))) $ firstify (sbvZipWith, atProxy (Proxy @(a, b, c)) "sbv.zipWith") (f, kindOf (Proxy @c))
 where concreteZipWith []     _      = Just []
       concreteZipWith _      []     = Just []
       concreteZipWith (a:as) (b:bs) = (:) <$> unliteral (literal a `f` literal b) <*> concreteZipWith as bs

       sbvZipWith uniq = def xs ys
         where def = smtFunction uniq $ \as bs -> ite (null as .|| null bs) nil (f (head as) (head bs) .: def (tail as) (tail bs))

-- | Concatenate list of lists.
--
-- >>> concat [[1..3::Integer], [4..7], [8..10]]
-- [1,2,3,4,5,6,7,8,9,10] :: [SInteger]
concat :: forall a. SymVal a => SList [a] -> SList a
concat l
  | Just l' <- unliteral l
  = literal (P.concat l')
  | True
  = def l
  where def = smtFunction (atProxy (Proxy @a) "sbv.concat") $
                          \xs -> ite (null xs) nil (let (h, t) = uncons xs in h ++ def t)

-- | Check all elements satisfy the predicate.
--
-- >>> let isEven x = x `sMod` 2 .== 0
-- >>> all isEven [2, 4, 6, 8, 10 :: Integer]
-- True
-- >>> all isEven [2, 4, 6, 1, 8, 10 :: Integer]
-- False
all :: forall a. SymVal a => (SBV a -> SBool) -> SList a -> SBool
all f l
 | Just l' <- unliteral l
 = sAll f (P.map literal l')
 | True
 = SBV $ SVal KBool $ firstify (sbvAll, atProxy (Proxy @a) "sbv.all") (f, KBool)
 where sbvAll uniq = def l
        where def = smtFunction uniq $ \xs -> ite (null xs) sTrue (let (h, t) = uncons xs in f h .&& def t)

-- | Check some element satisfies the predicate.
--
-- >>> let isEven x = x `sMod` 2 .== 0
-- >>> any (sNot . isEven) [2, 4, 6, 8, 10 :: Integer]
-- False
-- >>> any isEven [2, 4, 6, 1, 8, 10 :: Integer]
-- True
any :: forall a. SymVal a => (SBV a -> SBool) -> SList a -> SBool
any f l
 | Just l' <- unliteral l
 = sAny f (P.map literal l')
 | True
 = SBV $ SVal KBool $ firstify (sbvAny, atProxy (Proxy @a) "sbv.any") (f, KBool)
 where sbvAny uniq = def l
        where def = smtFunction uniq $ \xs -> ite (null xs) sFalse (let (h, t) = uncons xs in f h .|| def t)

-- | Conjunction of all the elements.
and :: SList Bool -> SBool
and = all id

-- | Disjunction of all the elements.
or :: SList Bool -> SBool
or = any id

-- | Replicate an element a given number of times.
--
-- >>> replicate 3 (2 :: SInteger) .== [2, 2, 2 :: Integer]
-- True
-- >>> replicate (-2) (2 :: SInteger) .== ([] :: SList Integer)
-- True
replicate :: forall a. SymVal a => SInteger -> SBV a -> SList a
replicate c e
 | Just c' <- unliteral c, Just e' <- unliteral e
 = literal (genericReplicate c' e')
 | True
 = def c e
 where def = smtFunction (atProxy (Proxy @a) "sbv.replicate") $
                         \count elt -> ite (count .<= 0) nil (elt .: def (count - 1) elt)

-- | Difference.
--
-- >>> [1, 2] \\ [3, 4]
-- [1,2] :: [SInteger]
-- >>> [1, 2] \\ [2, 4]
-- [1] :: [SInteger]
(\\) :: forall a. (Eq a, SymVal a) => SList a -> SList a -> SList a
xs \\ ys
 | Just xs' <- unliteral xs, Just ys' <- unliteral ys
 = literal (xs' L.\\ ys')
 | True
 = def xs ys
 where def = smtFunction (atProxy (Proxy @a) "sbv.diff") $
                         \x y -> ite (null x)
                                     nil
                                     (let (h, t) = uncons x
                                          r      = def t y
                                      in ite (h `elem` y) r (h .: r))
infix 5 \\  -- CPP: do not eat the final newline

-- | @filter f xs@ filters the list with the given predicate.
--
-- >>> filter (\x -> x `sMod` 2 .== 0) [1 .. 10 :: Integer]
-- [2,4,6,8,10] :: [SInteger]
-- >>> filter (\x -> x `sMod` 2 ./= 0) [1 .. 10 :: Integer]
-- [1,3,5,7,9] :: [SInteger]
filter :: forall a. SymVal a => (SBV a -> SBool) -> SList a -> SList a
filter f l
  | Just l' <- unliteral l, Just concResult <- concreteFilter l'
  = literal concResult
  | True
  = SBV $ SVal (kindOf (Proxy @(SList a))) $ firstify (sbvFilter, atProxy (Proxy @a) "sbv.filter") (f, KBool)
  where concreteFilter l' = case P.map (unliteral . f . literal) l' of
                              xs | P.any isNothing xs -> Nothing
                                 | True               -> Just [e | (True, e) <- P.zip (catMaybes xs) l']

        sbvFilter uniq = def l
          where def = smtFunction uniq $ \xs -> ite (null xs)
                                                    nil
                                                    (let (h, t) = uncons xs
                                                         r      = def t
                                                     in ite (f h) (h .: r) r)

-- | @partition f xs@ splits the list into two and returns those that satisfy the predicate in the
-- first element, and those that don't in the second.
partition :: forall a. SymVal a => (SBV a -> SBool) -> SList a -> STuple [a] [a]
partition f l
  | Just l' <- unliteral l, Just concResult <- concretePartition l'
  = concResult
  | True
  = SBV $ SVal (kindOf (Proxy @(STuple [a] [a]))) $ firstify (sbvPartition, atProxy (Proxy @a) "sbv.partition") (f, KBool)
  where concretePartition l' = case P.map (unliteral . f . literal) l' of
                                 xs | P.any isNothing xs -> Nothing
                                    | True               -> let (ts, fs) = L.partition fst (P.zip (catMaybes xs) l')
                                                            in Just $ tuple (literal (P.map snd ts), literal (P.map snd fs))

        sbvPartition uniq = def l
           where def = smtFunction uniq $ \xs -> ite (null xs)
                                                     (tuple (nil, nil))
                                                     (let (h, t)   = uncons xs
                                                          (as, bs) = untuple $ def t
                                                      in ite (f h)
                                                             (tuple (h .: as, bs))
                                                             (tuple (as, h .: bs)))

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
