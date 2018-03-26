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
       , strIsInfixOf
       , strIsPrefixOf
       , strIsSuffixOf
       , strReplace
       , strStrToNat
       , strNatToStr
       , strTake
       , strDrop
       , strMatch
       ) where

import Data.SBV.Core.Data
import Data.SBV.Core.Model

import Data.Char (isDigit)
import Data.List (genericLength, genericTake, genericDrop, tails, isPrefixOf, isSuffixOf, isInfixOf)

-- For doctest use only
import Data.SBV.Provers.Prover (sat, SatResult)
import Data.SBV.Utils.Boolean  ((&&&))

-- | Is the string concretely known empty?
isConcretelyEmpty :: SString -> Bool
isConcretelyEmpty ss | Just s <- unliteral ss = null s
                     | True                   = False

-- | Concatenate two strings. See also `.++`.
strConcat :: SString -> SString -> SString
strConcat x y | isConcretelyEmpty x = y
              | isConcretelyEmpty y = x
              | True                = lift2 StrConcat (Just (++)) x y

-- | Short cut for `strConcat`.
--
-- >>> :set -XOverloadedStrings
-- >>> sat $ \x y z -> strLen x .== 5 &&& strLen y .== 1 &&& x .++ y .++ z .== "Hello world!"
-- Satisfiable. Model:
--   s0 =  "Hello" :: String
--   s1 =      " " :: String
--   s2 = "world!" :: String
infixr 5 .++
(.++) :: SString -> SString -> SString
(.++) = strConcat

-- | Length of a string.
strLen :: SString -> SInteger
strLen = lift1 StrLen (Just (fromIntegral . length))

-- | `strSubstr s offset length` is the substring of @s@ at offset `offset` with length `length`.
-- This function is under-specified when the offset is outside the range of positions in @s@ or @length@
-- is negative or @offset+length@ exceeds the length of @s@. For a friendlier version of this function
-- that acts like Haskell's `take`, see `strTake`.
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

-- | @sub@ `strIsInfixOf` @s@. Does @s@ contain the substring @sub@?
strIsInfixOf :: SString -> SString -> SBool
strIsInfixOf s sub
  | isConcretelyEmpty sub
  = literal True
  | True
  = lift2 StrContains (Just isInfixOf) sub s -- NB. flip, since `StrContains` takes args in rev order!

-- | @pre@ `strIsPrefixOf` @s@. Is @pre@ a prefix of @s@?
strIsPrefixOf :: SString -> SString -> SBool
strIsPrefixOf pre s
  | isConcretelyEmpty pre
  = literal True
  | True
  = lift2 StrPrefixOf (Just isPrefixOf) pre s

-- | @suf@ `strIsSuffixOf` @s@. Is @suf@ a suffix of @s@?
strIsSuffixOf :: SString -> SString -> SBool
strIsSuffixOf suf s
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

-- | `strStrToNat s`. Retrieve integer encoded by string @s@ (ground rewriting only).
-- Note that by definition this function only works when 's' only contains digits,
-- that is, if it encodes a natural number. Otherwise, it returns '-1'.
-- See <http://cvc4.cs.stanford.edu/wiki/Strings> for details.
strStrToNat :: SString -> SInteger
strStrToNat s
 | Just a <- unliteral s
 = if all isDigit a
   then literal (read a)
   else -1
 | True
 = lift1 StrStrToNat Nothing s

-- | `strNatToStr i`. Retrieve string encoded by integer @i@ (ground rewriting only).
-- Again, only naturals are supported, any input that is not a natural number
-- produces empty string, even though we take an integer as an argument.
-- See <http://cvc4.cs.stanford.edu/wiki/Strings> for details.
strNatToStr :: SInteger -> SString
strNatToStr i
 | Just v <- unliteral i
 = literal $ if v >= 0 then show v else ""
 | True
 = lift1 StrNatToStr Nothing i

-- | `strTake len s`. Corresponds to Haskell's `take` on symbolic-strings.
strTake :: SInteger -> SString -> SString
strTake i s = ite (i .<= 0)        (literal "")
            $ ite (i .>= strLen s) s
            $ strSubstr s 0 i

-- | `strDrop len s`. Corresponds to Haskell's `drop` on symbolic-strings.
strDrop :: SInteger -> SString -> SString
strDrop i s = ite (i .>= ls) (literal "")
            $ ite (i .<= 0)  s
            $ strSubstr s i (ls - i)
  where ls = strLen s

-- | `strMatch s r` checks whether @s@ is in the language generated by @r@.
-- TODO: Currently SBV does *not* optimize this call if @s@ is concrete, but
-- rather directly defers down to the solver. We might want to perform the
-- operation on the Haskell side for performance reasons, should this become
-- important.
strMatch :: SString -> SRegExp -> SBool
strMatch s r = lift1 (StrInRe r) opt s
  where -- TODO: Replace this with a function that concretely evaluates the string against the
        -- reg-exp, possible future work. But probably there isn't enough ROI.
        opt :: Maybe (String -> Bool)
        opt = Nothing

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

-- | Make GHC not complain about doctest imports. Sigh..
__unused :: a
__unused = undefined (sat :: SBool -> IO SatResult)
                     ((&&&) :: SBool -> SBool -> SBool)
