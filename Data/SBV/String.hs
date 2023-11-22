-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.String
-- Copyright : (c) Joel Burget
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A collection of string/character utilities, useful when working
-- with symbolic strings. To the extent possible, the functions
-- in this module follow those of "Data.List" so importing qualified
-- is the recommended workflow. Also, it is recommended you use the
-- @OverloadedStrings@ extension to allow literal strings to be
-- used as symbolic-strings.
-----------------------------------------------------------------------------

{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.String (
        -- * Length, emptiness
          length, null
        -- * Deconstructing/Reconstructing
        , head, tail, uncons, init, singleton, strToStrAt, strToCharAt, (!!), implode, concat, (.:), snoc, nil, (++)
        -- * Containment
        , isInfixOf, isSuffixOf, isPrefixOf
        -- * Substrings
        , take, drop, subStr, replace, indexOf, offsetIndexOf
        -- * Reverse
        , reverse
        -- * Conversion to\/from naturals
        , strToNat, natToStr
        ) where

import Prelude hiding (head, tail, init, length, take, drop, concat, null, reverse, (++), (!!))
import qualified Prelude as P

import Data.SBV.Core.Data hiding (SeqOp(..))
import Data.SBV.Core.Data (SeqOp(SBVReverse))
import Data.SBV.Core.Model

import qualified Data.Char as C
import Data.List (genericLength, genericIndex, genericDrop, genericTake)
import qualified Data.List as L (tails, isSuffixOf, isPrefixOf, isInfixOf)

import Data.Proxy

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV
-- >>> import Prelude hiding (head, tail, init, length, take, drop, concat, null, reverse, (++), (!!))
-- >>> :set -XOverloadedStrings

-- | Length of a string.
--
-- >>> sat $ \s -> length s .== 2
-- Satisfiable. Model:
--   s0 = "BA" :: String
-- >>> sat $ \s -> length s .< 0
-- Unsatisfiable
-- >>> prove $ \s1 s2 -> length s1 + length s2 .== length (s1 ++ s2)
-- Q.E.D.
length :: SString -> SInteger
length = lift1 StrLen (Just (fromIntegral . P.length))

-- | @`null` s@ is True iff the string is empty
--
-- >>> prove $ \s -> null s .<=> length s .== 0
-- Q.E.D.
-- >>> prove $ \s -> null s .<=> s .== ""
-- Q.E.D.
null :: SString -> SBool
null s
  | Just cs <- unliteral s
  = literal (P.null cs)
  | True
  = s .== literal ""

-- | @`head`@ returns the head of a string. Unspecified if the string is empty.
--
-- >>> prove $ \c -> head (singleton c) .== c
-- Q.E.D.
head :: SString -> SChar
head = (`strToCharAt` 0)

-- | @`tail`@ returns the tail of a string. Unspecified if the string is empty.
--
-- >>> prove $ \h s -> tail (singleton h ++ s) .== s
-- Q.E.D.
-- >>> prove $ \s -> length s .> 0 .=> length (tail s) .== length s - 1
-- Q.E.D.
-- >>> prove $ \s -> sNot (null s) .=> singleton (head s) ++ tail s .== s
-- Q.E.D.
tail :: SString -> SString
tail s
 | Just (_:cs) <- unliteral s
 = literal cs
 | True
 = subStr s 1 (length s - 1)

-- | @`uncons` returns the pair of the first character and tail. Unspecified if the string is empty.
uncons :: SString -> (SChar, SString)
uncons l = (head l, tail l)

-- | @`init`@ returns all but the last element of the list. Unspecified if the string is empty.
--
-- >>> prove $ \c t -> init (t ++ singleton c) .== t
-- Q.E.D.
init :: SString -> SString
init s
 | Just cs@(_:_) <- unliteral s
 = literal $ P.init cs
 | True
 = subStr s 0 (length s - 1)

-- | @`singleton` c@ is the string of length 1 that contains the only character
-- whose value is the 8-bit value @c@.
--
-- >>> prove $ \c -> c .== literal 'A' .=> singleton c .== "A"
-- Q.E.D.
-- >>> prove $ \c -> length (singleton c) .== 1
-- Q.E.D.
singleton :: SChar -> SString
singleton = lift1 StrUnit (Just wrap)
  where wrap c = [c]

-- | @`strToStrAt` s offset@. Substring of length 1 at @offset@ in @s@. Unspecified if
-- offset is out of bounds.
--
-- >>> prove $ \s1 s2 -> strToStrAt (s1 ++ s2) (length s1) .== strToStrAt s2 0
-- Q.E.D.
-- >>> sat $ \s -> length s .>= 2 .&& strToStrAt s 0 ./= strToStrAt s (length s - 1)
-- Satisfiable. Model:
--   s0 = "AB" :: String
strToStrAt :: SString -> SInteger -> SString
strToStrAt s offset = subStr s offset 1

-- | @`strToCharAt` s i@ is the 8-bit value stored at location @i@. Unspecified if
-- index is out of bounds.
--
-- >>> prove $ \i -> i .>= 0 .&& i .<= 4 .=> "AAAAA" `strToCharAt` i .== literal 'A'
-- Q.E.D.
strToCharAt :: SString -> SInteger -> SChar
strToCharAt s i
  | Just cs <- unliteral s, Just ci <- unliteral i, ci >= 0, ci < genericLength cs, let c = C.ord (cs `genericIndex` ci)
  = literal (C.chr c)
  | True
  = lift2 StrNth Nothing s i

-- | Short cut for 'strToCharAt'
(!!) :: SString -> SInteger -> SChar
(!!) = strToCharAt

-- | @`implode` cs@ is the string of length @|cs|@ containing precisely those
-- characters. Note that there is no corresponding function @explode@, since
-- we wouldn't know the length of a symbolic string.
--
-- >>> prove $ \c1 c2 c3 -> length (implode [c1, c2, c3]) .== 3
-- Q.E.D.
-- >>> prove $ \c1 c2 c3 -> map (strToCharAt (implode [c1, c2, c3])) (map literal [0 .. 2]) .== [c1, c2, c3]
-- Q.E.D.
implode :: [SChar] -> SString
implode = foldr ((++) . singleton) ""

-- | Prepend an element, the traditional @cons@.
infixr 5 .:
(.:) :: SChar -> SString -> SString
c .: cs = singleton c ++ cs

-- | Append an element
snoc :: SString -> SChar -> SString
s `snoc` c = s ++ singleton c

-- | Empty string. This value has the property that it's the only string with length 0:
--
-- >>> prove $ \l -> length l .== 0 .<=> l .== nil
-- Q.E.D.
nil :: SString
nil = ""

-- | Concatenate two strings. See also `++`.
concat :: SString -> SString -> SString
concat x y | isConcretelyEmpty x = y
           | isConcretelyEmpty y = x
           | True                = lift2 StrConcat (Just (P.++)) x y

-- | Short cut for `concat`.
--
-- >>> sat $ \x y z -> length x .== 5 .&& length y .== 1 .&& x ++ y ++ z .== "Hello world!"
-- Satisfiable. Model:
--   s0 =  "Hello" :: String
--   s1 =      " " :: String
--   s2 = "world!" :: String
infixr 5 ++
(++) :: SString -> SString -> SString
(++) = concat

-- | @`isInfixOf` sub s@. Does @s@ contain the substring @sub@?
--
-- >>> prove $ \s1 s2 s3 -> s2 `isInfixOf` (s1 ++ s2 ++ s3)
-- Q.E.D.
-- >>> prove $ \s1 s2 -> s1 `isInfixOf` s2 .&& s2 `isInfixOf` s1 .<=> s1 .== s2
-- Q.E.D.
isInfixOf :: SString -> SString -> SBool
sub `isInfixOf` s
  | isConcretelyEmpty sub
  = literal True
  | True
  = lift2 StrContains (Just (flip L.isInfixOf)) s sub -- NB. flip, since `StrContains` takes args in rev order!

-- | @`isPrefixOf` pre s@. Is @pre@ a prefix of @s@?
--
-- >>> prove $ \s1 s2 -> s1 `isPrefixOf` (s1 ++ s2)
-- Q.E.D.
-- >>> prove $ \s1 s2 -> s1 `isPrefixOf` s2 .=> subStr s2 0 (length s1) .== s1
-- Q.E.D.
isPrefixOf :: SString -> SString -> SBool
pre `isPrefixOf` s
  | isConcretelyEmpty pre
  = literal True
  | True
  = lift2 StrPrefixOf (Just L.isPrefixOf) pre s

-- | @`isSuffixOf` suf s@. Is @suf@ a suffix of @s@?
--
-- >>> prove $ \s1 s2 -> s2 `isSuffixOf` (s1 ++ s2)
-- Q.E.D.
-- >>> prove $ \s1 s2 -> s1 `isSuffixOf` s2 .=> subStr s2 (length s2 - length s1) (length s1) .== s1
-- Q.E.D.
isSuffixOf :: SString -> SString -> SBool
suf `isSuffixOf` s
  | isConcretelyEmpty suf
  = literal True
  | True
  = lift2 StrSuffixOf (Just L.isSuffixOf) suf s

-- | @`take` len s@. Corresponds to Haskell's `take` on symbolic-strings.
--
-- >>> prove $ \s i -> i .>= 0 .=> length (take i s) .<= i
-- Q.E.D.
take :: SInteger -> SString -> SString
take i s = ite (i .<= 0)        (literal "")
         $ ite (i .>= length s) s
         $ subStr s 0 i

-- | @`drop` len s@. Corresponds to Haskell's `drop` on symbolic-strings.
--
-- >>> prove $ \s i -> length (drop i s) .<= length s
-- Q.E.D.
-- >>> prove $ \s i -> take i s ++ drop i s .== s
-- Q.E.D.
drop :: SInteger -> SString -> SString
drop i s = ite (i .>= ls) (literal "")
         $ ite (i .<= 0)  s
         $ subStr s i (ls - i)
  where ls = length s

-- | @`subStr` s offset len@ is the substring of @s@ at offset @offset@ with length @len@.
-- This function is under-specified when the offset is outside the range of positions in @s@ or @len@
-- is negative or @offset+len@ exceeds the length of @s@.
--
-- >>> prove $ \s i -> i .>= 0 .&& i .< length s .=> subStr s 0 i ++ subStr s i (length s - i) .== s
-- Q.E.D.
-- >>> sat  $ \i j -> subStr "hello" i j .== "ell"
-- Satisfiable. Model:
--   s0 = 1 :: Integer
--   s1 = 3 :: Integer
-- >>> sat  $ \i j -> subStr "hell" i j .== "no"
-- Unsatisfiable
subStr :: SString -> SInteger -> SInteger -> SString
subStr s offset len
  | Just c <- unliteral s                    -- a constant string
  , Just o <- unliteral offset               -- a constant offset
  , Just l <- unliteral len                  -- a constant length
  , let lc = genericLength c                 -- length of the string
  , let valid x = x >= 0 && x <= lc          -- predicate that checks valid point
  , valid o                                  -- offset is valid
  , l >= 0                                   -- length is not-negative
  , valid $ o + l                            -- we don't overrun
  = literal $ genericTake l $ genericDrop o c
  | True                                     -- either symbolic, or something is out-of-bounds
  = lift3 StrSubstr Nothing s offset len

-- | @`replace` s src dst@. Replace the first occurrence of @src@ by @dst@ in @s@
--
-- >>> prove $ \s -> replace "hello" s "world" .== "world" .=> s .== "hello"
-- Q.E.D.
-- >>> prove $ \s1 s2 s3 -> length s2 .> length s1 .=> replace s1 s2 s3 .== s1
-- Q.E.D.
replace :: SString -> SString -> SString -> SString
replace s src dst
  | Just b <- unliteral src, P.null b   -- If src is null, simply prepend
  = dst ++ s
  | Just a <- unliteral s
  , Just b <- unliteral src
  , Just c <- unliteral dst
  = literal $ walk a b c
  | True
  = lift3 StrReplace Nothing s src dst
  where walk haystack needle newNeedle = go haystack   -- note that needle is guaranteed non-empty here.
           where go []       = []
                 go i@(c:cs)
                  | needle `L.isPrefixOf` i = newNeedle P.++ genericDrop (genericLength needle :: Integer) i
                  | True                    = c : go cs

-- | @`indexOf` s sub@. Retrieves first position of @sub@ in @s@, @-1@ if there are no occurrences.
-- Equivalent to @`offsetIndexOf` s sub 0@.
--
-- >>> prove $ \s1 s2 -> length s2 .> length s1 .=> indexOf s1 s2 .== -1
-- Q.E.D.
indexOf :: SString -> SString -> SInteger
indexOf s sub = offsetIndexOf s sub 0

-- | @`offsetIndexOf` s sub offset@. Retrieves first position of @sub@ at or
-- after @offset@ in @s@, @-1@ if there are no occurrences.
--
-- >>> prove $ \s sub -> offsetIndexOf s sub 0 .== indexOf s sub
-- Q.E.D.
-- >>> prove $ \s sub i -> i .>= length s .&& length sub .> 0 .=> offsetIndexOf s sub i .== -1
-- Q.E.D.
-- >>> prove $ \s sub i -> i .> length s .=> offsetIndexOf s sub i .== -1
-- Q.E.D.
offsetIndexOf :: SString -> SString -> SInteger -> SInteger
offsetIndexOf s sub offset
  | Just c <- unliteral s               -- a constant string
  , Just n <- unliteral sub             -- a constant search pattern
  , Just o <- unliteral offset          -- at a constant offset
  , o >= 0, o <= genericLength c        -- offset is good
  = case [i | (i, t) <- zip [o ..] (L.tails (genericDrop o c)), n `L.isPrefixOf` t] of
      (i:_) -> literal i
      _     -> -1
  | True
  = lift3 StrIndexOf Nothing s sub offset

-- | @`reverse` s@ reverses the string.
-- >>> sat $ \s -> reverse s .== "abc"
-- Satisfiable. Model:
--   s0 = "cba" :: String
-- >>> prove $ \s -> reverse s .== "" .<=> null s
-- Q.E.D.
reverse :: SString -> SString
reverse s
  | Just s' <- unliteral s
  = literal (P.reverse s')
  | True
  = SBV $ SVal KString $ Right $ cache r
  where r st = do sva <- sbvToSV st s
                  newExpr st KString (SBVApp (SeqOp (SBVReverse KString)) [sva])

-- | @`strToNat` s@. Retrieve integer encoded by string @s@ (ground rewriting only).
-- Note that by definition this function only works when @s@ only contains digits,
-- that is, if it encodes a natural number. Otherwise, it returns '-1'.
--
-- >>> prove $ \s -> let n = strToNat s in length s .== 1 .=> (-1) .<= n .&& n .<= 9
-- Q.E.D.
strToNat :: SString -> SInteger
strToNat s
 | Just a <- unliteral s
 = if all C.isDigit a && not (P.null a)
   then literal (read a)
   else -1
 | True
 = lift1 StrStrToNat Nothing s

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
 = lift1 StrNatToStr Nothing i

-- | Lift a unary operator over strings.
lift1 :: forall a b. (SymVal a, SymVal b) => StrOp -> Maybe (a -> b) -> SBV a -> SBV b
lift1 w mbOp a
  | Just cv <- concEval1 mbOp a
  = cv
  | True
  = SBV $ SVal k $ Right $ cache r
  where k = kindOf (Proxy @b)
        r st = do sva <- sbvToSV st a
                  newExpr st k (SBVApp (StrOp w) [sva])

-- | Lift a binary operator over strings.
lift2 :: forall a b c. (SymVal a, SymVal b, SymVal c) => StrOp -> Maybe (a -> b -> c) -> SBV a -> SBV b -> SBV c
lift2 w mbOp a b
  | Just cv <- concEval2 mbOp a b
  = cv
  | True
  = SBV $ SVal k $ Right $ cache r
  where k = kindOf (Proxy @c)
        r st = do sva <- sbvToSV st a
                  svb <- sbvToSV st b
                  newExpr st k (SBVApp (StrOp w) [sva, svb])

-- | Lift a ternary operator over strings.
lift3 :: forall a b c d. (SymVal a, SymVal b, SymVal c, SymVal d) => StrOp -> Maybe (a -> b -> c -> d) -> SBV a -> SBV b -> SBV c -> SBV d
lift3 w mbOp a b c
  | Just cv <- concEval3 mbOp a b c
  = cv
  | True
  = SBV $ SVal k $ Right $ cache r
  where k = kindOf (Proxy @d)
        r st = do sva <- sbvToSV st a
                  svb <- sbvToSV st b
                  svc <- sbvToSV st c
                  newExpr st k (SBVApp (StrOp w) [sva, svb, svc])

-- | Concrete evaluation for unary ops
concEval1 :: (SymVal a, SymVal b) => Maybe (a -> b) -> SBV a -> Maybe (SBV b)
concEval1 mbOp a = literal <$> (mbOp <*> unliteral a)

-- | Concrete evaluation for binary ops
concEval2 :: (SymVal a, SymVal b, SymVal c) => Maybe (a -> b -> c) -> SBV a -> SBV b -> Maybe (SBV c)
concEval2 mbOp a b = literal <$> (mbOp <*> unliteral a <*> unliteral b)

-- | Concrete evaluation for ternary ops
concEval3 :: (SymVal a, SymVal b, SymVal c, SymVal d) => Maybe (a -> b -> c -> d) -> SBV a -> SBV b -> SBV c -> Maybe (SBV d)
concEval3 mbOp a b c = literal <$> (mbOp <*> unliteral a <*> unliteral b <*> unliteral c)

-- | Is the string concretely known empty?
isConcretelyEmpty :: SString -> Bool
isConcretelyEmpty ss | Just s <- unliteral ss = P.null s
                     | True                   = False

{- HLint ignore implode "Use concatMap" -}
