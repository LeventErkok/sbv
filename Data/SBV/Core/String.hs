{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Core.String
-- Copyright   :  (c) Joel Burget
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Implementation of string operations mapping to SMT-Lib2 strings
-----------------------------------------------------------------------------

module Data.SBV.Core.String (
         strConcat, (.++)
       , strLen
       , strSubstr
       , strIndexOf
       , strOffsetIndexOf
       , strAt
       , strContains
       , strPrefixOf
       , strSuffixOf
       , strReplace
       , strToInt
       , intToStr
       ) where

import Data.SBV.Core.Data
import Data.SBV.Core.Model ()
import Data.SBV.Core.Symbolic

import Data.Char (isDigit)
import Data.List (genericLength, genericTake, genericDrop, tails, isPrefixOf, isSuffixOf, isInfixOf)

-- | Is the string concretely known empty?
isConcretelyEmpty :: SString -> Bool
isConcretelyEmpty ss | Just s <- unliteral ss = null s
                     | True                   = False

-- | Concatenate two strings
strConcat :: SString -> SString -> SString
strConcat x y | isConcretelyEmpty x = y
              | isConcretelyEmpty y = x
              | True                = lift2 StrConcat (Just (++)) x y

-- | Short cut for `strConcat`.
infixr 5 .++
(.++) :: SString -> SString -> SString
(.++) = strConcat

-- | Length of a string.
strLen :: SString -> SInteger
strLen = lift1 StrLen (Just (fromIntegral . length))

-- | `strSubStr s offset length` is the substring of @s@ at offset `offset` with length `length`.
-- This function is under-specified when the offset is outside the range of positions in @s@ or @length@
-- is negative or @offset+length@ exceeds the length of @s@.
strSubstr :: SString -> SInteger -> SInteger -> SString
strSubstr s offset len
  | Just c <- unliteral s                    -- a constant string
  , Just o <- unliteral offset               -- a constant offset
  , Just l <- unliteral len                  -- a constant length
  , let lc = genericLength c                 -- length of the string
  , let valid x = x >= 0 && x < lc           -- predicate that checks valid point
  , valid o                                  -- offset is valid
  , l >= 0                                   -- length is not-negative
  , valid $ o + l - 1                        -- we don't overrun
  = literal $ genericTake l $ genericDrop o c
  | True                                     -- either symbolic, or something is out-of-bounds
  = lift3 StrSubstr Nothing s offset len

-- | `strIndexOf s sub`. Retrieves first position of @sub@ in @s@, @-1@ if there are no occurrences.
-- Equivalent to `strOffsetIndexOf s sub 0`.
strIndexOf :: SString -> SString -> SInteger
strIndexOf s sub = strOffsetIndexOf s sub 0

-- | `strOffsetIndexOf s sub offset`. Retrieves first position of @sub@ at or after @offset@ in @s@, @-1@ if there are no occurrences.
strOffsetIndexOf :: SString -> SString -> SInteger -> SInteger
strOffsetIndexOf s sub offset
  | Just c <- unliteral s               -- a constant string
  , Just n <- unliteral sub             -- a constant search pattern
  , Just o <- unliteral offset          -- at a constant offset
  , o >= 0, o < genericLength c         -- offset is good
  = case [i | (i, t) <- zip [o ..] (tails (genericDrop o c)), n `isPrefixOf` t] of
      (i:_) -> literal i
      _     -> -1
  | True
  = lift3 StrIndexOf Nothing sub s offset

-- | `strAt s offset`. Substring of length 1 at @offset@ in @s@. Note that this is rather odd
-- as it returns a string; one would expect a character instead. But we're following the SMTLib theory
-- here and returning a string, and also we don't really have an 'SChar' type to start with anyhow.
strAt :: SString -> SInteger -> SString
strAt s offset = strSubstr s offset 1

-- | `strContains s sub`. Does @s@ contain the substring @sub@? Note the reversal here!
-- We're sticking to SMTLib convention, as opposed to Haskell's `isInfixOf`/`isSuffixOf`
-- and also `strPrefixOf` and `strSuffixOf` below. Unfortunate, we are staying consistent
-- with the corresponding SMTLib function.
strContains :: SString -> SString -> SBool
strContains s sub
  | isConcretelyEmpty sub
  = literal True
  | True
  = lift2 StrContains (Just (flip isInfixOf)) s sub  -- NB. flip!

-- | `strPrefixOf pre s`. Is @pre@ a prefix of @s@?
strPrefixOf :: SString -> SString -> SBool
strPrefixOf pre s
  | isConcretelyEmpty pre
  = literal True
  | True
  = lift2 StrPrefixOf (Just isPrefixOf) pre s

-- | `strSuffixOf suf s`. Is @suf@ a suffix of @s@?
strSuffixOf :: SString -> SString -> SBool
strSuffixOf suf s
  | isConcretelyEmpty suf
  = literal True
  | True
  = lift2 StrSuffixOf (Just isSuffixOf) suf s

-- | `strReplace s src dst`. Replace the first occurrence of @src@ by @dst@ in @s@
strReplace :: SString -> SString -> SString -> SString
strReplace s src dst
  | Just a <- unliteral s
  , Just b <- unliteral src
  , Just c <- unliteral dst
  = literal $ walk a b c
  | True
  = lift3 StrReplace Nothing s src dst
  where walk haystack needle newNeedle = go haystack
           where go []       = []
                 go i@(c:cs)
                  | needle `isPrefixOf` i = newNeedle ++ drop (length needle) i
                  | True                  = c : go cs

-- | `strToInt s`. Retrieve integer encoded by string @s@ (ground rewriting only).
-- Note that by definition this function only works when 's' only contains digits,
-- that is, if it encodes a natural number. Otherwise, it returns '-1'.
-- The confusing name is unfortunate, but we are sticking to the SMTLib semantics again.
-- See <http://cvc4.cs.stanford.edu/wiki/Strings> for details.
strToInt :: SString -> SInteger
strToInt s
 | Just a <- unliteral s
 = if all isDigit a
   then literal (read a)
   else -1
 | True
 = lift1 StrToInt Nothing s

-- | `intToStr i`. Retrieve string encoded by integer @i@ (ground rewriting only).
-- Again, only naturals are supported, any input that is not a natural number
-- produces empty string.
-- See <http://cvc4.cs.stanford.edu/wiki/Strings> for details.
intToStr :: SInteger -> SString
intToStr i
 | Just v <- unliteral i
 = literal $ if v >= 0 then show v else ""
 | True
 = lift1 IntToStr Nothing i

-- | Lift a unary operator over strings.
lift1 :: forall a b. (SymWord a, SymWord b) => StrOp -> Maybe (a -> b) -> SBV a -> SBV b
lift1 w mbOp a
  | Just cv <- concEval1 mbOp a
  = cv
  | True
  = SBV $ SVal k $ Right $ cache r
  where k = kindOf (undefined :: b)
        r st = do swa <- sbvToSW st a
                  newExpr st k (SBVApp (StrOp w) [swa])

-- | Lift a binary operator over strings.
lift2 :: forall a b c. (SymWord a, SymWord b, SymWord c) => StrOp -> Maybe (a -> b -> c) -> SBV a -> SBV b -> SBV c
lift2 w mbOp a b
  | Just cv <- concEval2 mbOp a b
  = cv
  | True
  = SBV $ SVal k $ Right $ cache r
  where k = kindOf (undefined :: c)
        r st = do swa <- sbvToSW st a
                  swb <- sbvToSW st b
                  newExpr st k (SBVApp (StrOp w) [swa, swb])

-- | Lift a ternary operator over strings.
lift3 :: forall a b c d. (SymWord a, SymWord b, SymWord c, SymWord d) => StrOp -> Maybe (a -> b -> c -> d) -> SBV a -> SBV b -> SBV c -> SBV d
lift3 w mbOp a b c
  | Just cv <- concEval3 mbOp a b c
  = cv
  | True
  = SBV $ SVal k $ Right $ cache r
  where k = kindOf (undefined :: d)
        r st = do swa <- sbvToSW st a
                  swb <- sbvToSW st b
                  swc <- sbvToSW st c
                  newExpr st k (SBVApp (StrOp w) [swa, swb, swc])

-- | Concrete evaluation for unary ops
concEval1 :: (SymWord a, SymWord b) => Maybe (a -> b) -> SBV a -> Maybe (SBV b)
concEval1 mbOp a = literal <$> (mbOp <*> unliteral a)

-- | Concrete evaluation for binary ops
concEval2 :: (SymWord a, SymWord b, SymWord c) => Maybe (a -> b -> c) -> SBV a -> SBV b -> Maybe (SBV c)
concEval2 mbOp a b = literal <$> (mbOp <*> unliteral a <*> unliteral b)

-- | Concrete evaluation for ternary ops
concEval3 :: (SymWord a, SymWord b, SymWord c, SymWord d) => Maybe (a -> b -> c -> d) -> SBV a -> SBV b -> SBV c -> Maybe (SBV d)
concEval3 mbOp a b c = literal <$> (mbOp <*> unliteral a <*> unliteral b <*> unliteral c)
