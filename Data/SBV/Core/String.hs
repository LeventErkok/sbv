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
       , strNull
       , w8ToStr
       , strToW8At
       , strHead
       , strTail
       ) where

import Data.SBV.Core.Data
import Data.SBV.Core.Model

import Data.Char (isDigit, chr, ord)
import Data.List (genericLength, genericTake, genericDrop, genericIndex, tails, isPrefixOf, isSuffixOf, isInfixOf)

-- For doctest use only
import Data.SBV.Provers.Prover (sat, prove, SatResult, ThmResult)
import Data.SBV.Utils.Boolean  ((&&&), (==>), (<=>), bnot)

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
--
-- >>> sat $ \s -> strLen s .== 2
-- Satisfiable. Model:
--   s0 = "\NUL\NUL" :: String
-- >>> sat $ \s -> strLen s .< 0
-- Unsatisfiable
-- >>> prove $ \s1 s2 -> strLen s1 + strLen s2 .== strLen (s1 .++ s2)
-- Q.E.D.
strLen :: SString -> SInteger
strLen = lift1 StrLen (Just (fromIntegral . length))

-- | @`strSubstr` s offset len@ is the substring of @s@ at offset `offset` with length `len`.
-- This function is under-specified when the offset is outside the range of positions in @s@ or @len@
-- is negative or @offset+len@ exceeds the length of @s@. For a friendlier version of this function
-- that acts like Haskell's `take`\/`drop`, see `strTake`\/`strDrop`.
--
-- >>> :set -XOverloadedStrings
-- >>> prove $ \s i -> i .>= 0 &&& i .< strLen s ==> strSubstr s 0 i .++ strSubstr s i (strLen s - i) .== s
-- Q.E.D.
-- >>> sat  $ \i j -> strSubstr "hello" i j .== "ell"
-- Satisfiable. Model:
--   s0 = 1 :: Integer
--   s1 = 3 :: Integer
-- >>> sat  $ \i j -> strSubstr "hell" i j .== "no"
-- Unsatisfiable
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

-- | @`strIndexOf` s sub@. Retrieves first position of @sub@ in @s@, @-1@ if there are no occurrences.
-- Equivalent to @`strOffsetIndexOf` s sub 0@.
--
-- >>> prove $ \s i -> i .> 0 &&& i .< strLen s ==> strIndexOf s (strSubstr s i 1) .<= i
-- Q.E.D.
-- >>> prove $ \s i -> i .> 0 &&& i .< strLen s ==> strIndexOf s (strSubstr s i 1) .== i
-- Falsifiable. Counter-example:
--   s0 = "\NUL\NUL\NUL" :: String
--   s1 =              2 :: Integer
strIndexOf :: SString -> SString -> SInteger
strIndexOf s sub = strOffsetIndexOf s sub 0

-- | @`strOffsetIndexOf` s sub offset@. Retrieves first position of @sub@ at or
-- after @offset@ in @s@, @-1@ if there are no occurrences.
--
-- >>> prove $ \s sub -> strOffsetIndexOf s sub 0 .== strIndexOf s sub
-- Q.E.D.
-- >>> prove $ \s sub i -> i .>= strLen s &&& strLen sub .> 0 ==> strOffsetIndexOf s sub i .== -1
-- Q.E.D.
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
  = lift3 StrIndexOf Nothing s sub offset

-- | @`strAt` s offset@. Substring of length 1 at @offset@ in @s@. Note that this is rather odd
-- as it returns a string; one would expect a character instead. But we're following the SMTLib theory
-- here and returning a string, and also we don't really have an 'SChar' type to start with anyhow.
--
-- >>> prove $ \s1 s2 -> strAt (strConcat s1 s2) (strLen s1) .== strAt s2 0
-- Q.E.D.
-- >>> sat $ \s -> strLen s .>= 2 &&& strAt s 0 ./= strAt s (strLen s - 1)
-- Satisfiable. Model:
--   s0 = "\NUL\NUL " :: String
strAt :: SString -> SInteger -> SString
strAt s offset = strSubstr s offset 1

-- | @`strIsInfixOf` sub s@. Does @s@ contain the substring @sub@?
--
-- >>> prove $ \s1 s2 s3 -> s2 `strIsInfixOf` (s1 .++ s2 .++ s3)
-- Q.E.D.
-- >>> prove $ \s1 s2 -> s1 `strIsInfixOf` s2 &&& s2 `strIsInfixOf` s1 <=> s1 .== s2
-- Q.E.D.
strIsInfixOf :: SString -> SString -> SBool
sub `strIsInfixOf` s
  | isConcretelyEmpty sub
  = literal True
  | True
  = lift2 StrContains (Just isInfixOf) s sub -- NB. flip, since `StrContains` takes args in rev order!

-- | @`strIsPrefixOf` pre s@. Is @pre@ a prefix of @s@?
--
-- >>> prove $ \s1 s2 -> s1 `strIsPrefixOf` (s1 .++ s2)
-- Q.E.D.
-- >>> prove $ \s1 s2 -> s1 `strIsPrefixOf` s2 ==> strSubstr s2 0 (strLen s1) .== s1
-- Q.E.D.
strIsPrefixOf :: SString -> SString -> SBool
pre `strIsPrefixOf` s
  | isConcretelyEmpty pre
  = literal True
  | True
  = lift2 StrPrefixOf (Just isPrefixOf) pre s

-- | @`strIsSuffixOf` suf s@. Is @suf@ a suffix of @s@?
--
-- >>> prove $ \s1 s2 -> s2 `strIsSuffixOf` (s1 .++ s2)
-- Q.E.D.
-- >>> prove $ \s1 s2 -> s1 `strIsSuffixOf` s2 ==> strSubstr s2 (strLen s2 - strLen s1) (strLen s1) .== s1
-- Q.E.D.
strIsSuffixOf :: SString -> SString -> SBool
suf `strIsSuffixOf` s
  | isConcretelyEmpty suf
  = literal True
  | True
  = lift2 StrSuffixOf (Just isSuffixOf) suf s

-- | @`strReplace` s src dst@. Replace the first occurrence of @src@ by @dst@ in @s@
--
-- >>> prove $ \s -> strReplace "hello" s "world" .== "world" ==> s .== "hello"
-- Q.E.D.
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

-- | @`strStrToNat` s@. Retrieve integer encoded by string @s@ (ground rewriting only).
-- Note that by definition this function only works when 's' only contains digits,
-- that is, if it encodes a natural number. Otherwise, it returns '-1'.
-- See <http://cvc4.cs.stanford.edu/wiki/Strings> for details.
--
-- >>> prove $ \s -> let n = strStrToNat s in n .>= 0 &&& n .< 10 ==> strLen s .== 1
-- Q.E.D.
strStrToNat :: SString -> SInteger
strStrToNat s
 | Just a <- unliteral s
 = if all isDigit a
   then literal (read a)
   else -1
 | True
 = lift1 StrStrToNat Nothing s

-- | @`strNatToStr` i@. Retrieve string encoded by integer @i@ (ground rewriting only).
-- Again, only naturals are supported, any input that is not a natural number
-- produces empty string, even though we take an integer as an argument.
-- See <http://cvc4.cs.stanford.edu/wiki/Strings> for details.
--
-- >>> prove $ \i -> strLen (strNatToStr i) .== 3 ==> i .<= 999
-- Q.E.D.
strNatToStr :: SInteger -> SString
strNatToStr i
 | Just v <- unliteral i
 = literal $ if v >= 0 then show v else ""
 | True
 = lift1 StrNatToStr Nothing i

-- | @`strTake` len s@. Corresponds to Haskell's `take` on symbolic-strings.
--
-- >>> prove $ \s i -> i .>= 0 ==> strLen (strTake i s) .<= i
-- Q.E.D.
strTake :: SInteger -> SString -> SString
strTake i s = ite (i .<= 0)        (literal "")
            $ ite (i .>= strLen s) s
            $ strSubstr s 0 i

-- | @`strDrop` len s@. Corresponds to Haskell's `drop` on symbolic-strings.
--
-- >>> prove $ \s i -> strLen (strDrop i s) .<= strLen s
-- Q.E.D.
-- >>> prove $ \s i -> strTake i s .++ strDrop i s .== s
-- Q.E.D.
strDrop :: SInteger -> SString -> SString
strDrop i s = ite (i .>= ls) (literal "")
            $ ite (i .<= 0)  s
            $ strSubstr s i (ls - i)
  where ls = strLen s

-- | @`strNull` s@ is True iff the string is empty
--
-- >>> prove $ \s -> strNull s <=> strLen s .== 0
-- Q.E.D.
-- >>> :set -XOverloadedStrings
-- >>> prove $ \s -> strNull s <=> s .== ""
-- Q.E.D.
strNull :: SString -> SBool
strNull s
  | Just cs <- unliteral s
  = literal (null cs)
  | True
  = strLen s .== 0

-- | @`w8ToStr` c@ is the string of length 1 that contains the only character
-- whose value is the 8-bit value @c@.
--
-- >>> :set -XOverloadedStrings
-- >>> prove $ \c -> c .== 65 ==> w8ToStr c .== "A"
-- Q.E.D.
-- >>> prove $ \c -> strLen (w8ToStr c) .== 1
-- Q.E.D.
w8ToStr :: SWord8 -> SString
w8ToStr = lift1 StrUnit (Just $ \cv -> [chr (fromIntegral cv)])

-- | @`strToW8At` s i@ is the 8-bit value stored at location @i@. Unspecified if
-- index is out of bounds.
--
-- >>> :set -XOverloadedStrings
-- >>> prove $ \i -> i .>= 0 &&& i .<= 4 ==> "AAAAA" `strToW8At` i .== 65
-- Q.E.D.
-- >>> prove $ \s i c -> s `strToW8At` i .== c ==> strIndexOf s (w8ToStr c) .<= i
-- Q.E.D.
strToW8At :: SString -> SInteger -> SWord8
strToW8At s i
  | Just cs <- unliteral s, Just ci <- unliteral i, ci >= 0, ci < genericLength cs, let c = ord (cs `genericIndex` ci), c >= 0, c < 256
  = literal (fromIntegral c)
  | True
  = SBV (SVal w8 (Right (cache (y (s `strAt` i)))))
  where w8      = KBounded False 8
        -- This is tricker than it needs to be, but necessary since there's
        -- no SMTLib function to extract the character from a string. Instead,
        -- we form a singleton string, and assert that it is equivalent to
        -- the extracted value. See <http://github.com/Z3Prover/z3/issues/1302>
        y si st = do c <- internalVariable st w8
                     cs <- newExpr st KString (SBVApp (StrOp StrUnit) [c])
                     let csSBV = SBV (SVal KString (Right (cache (\_ -> return cs))))
                     internalConstraint st Nothing $ unSBV $ csSBV .== si
                     return c

-- | @`strHead`@ returns the head of a string. Unspecified if the string is empty.
--
-- >>> prove $ \c -> strHead (w8ToStr c) .== c
-- Q.E.D.
strHead :: SString -> SWord8
strHead = (`strToW8At` 0)

-- | @`strTail`@ returns the tail of a string. Unspecified if the string is empty.
--
-- >>> prove $ \h s -> strTail (w8ToStr h .++ s) .== s
-- Q.E.D.
-- >>> prove $ \s -> strLen s .> 0 ==> strLen (strTail s) .== strLen s - 1
-- Q.E.D.
-- >>> prove $ \s -> bnot (strNull s) ==> w8ToStr (strHead s) .++ strTail s .== s
-- Q.E.D.
strTail :: SString -> SString
strTail s
 | Just (_:cs) <- unliteral s
 = literal cs
 | True
 = strSubstr s 1 (strLen s - 1)

-- | @`strMatch` s r@ checks whether @s@ is in the language generated by @r@.
-- TODO: Currently SBV does *not* optimize this call if @s@ is concrete, but
-- rather directly defers down to the solver. We might want to perform the
-- operation on the Haskell side for performance reasons, should this become
-- important.
--
-- For instance, you can generate valid-looking phone numbers like this:
--
-- > let dig09 = RE_Range '0' '9'
-- > let dig19 = RE_Range '1' '9'
-- > let pre   = dig19 `RE_Conc` RE_Loop 2 2 dig09
-- > let post  = dig19 `RE_Conc` RE_Loop 3 3 dig09
-- > let phone = pre `RE_Conc` RE_Literal "-" `RE_Conc` post
-- > sat (`strMatch` phone)
-- > Satisfiable. Model:
-- >   s0 = "222-2248" :: String
--
-- >>> :set -XOverloadedStrings
-- >>> prove $ \s -> strMatch s (RE_Literal "hello") <=> s .== "hello"
-- Q.E.D.
-- >>> prove $ \s -> strMatch s (RE_Loop 2 5 (RE_Literal "xyz")) ==> strLen s .>= 6
-- Q.E.D.
-- >>> prove $ \s -> strMatch s (RE_Loop 2 5 (RE_Literal "xyz")) ==> strLen s .<= 15
-- Q.E.D.
-- >>> prove $ \s -> strMatch s (RE_Loop 2 5 (RE_Literal "xyz")) ==> strLen s .>= 7
-- Falsifiable. Counter-example:
--   s0 = "xyzxyz" :: String
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
__unused = undefined (sat   :: SBool -> IO SatResult)
                     (prove :: SBool -> IO ThmResult)
                     ((&&&) :: SBool -> SBool -> SBool)
                     ((==>) :: SBool -> SBool -> SBool)
                     ((<=>) :: SBool -> SBool -> SBool)
                     (bnot  :: SBool -> SBool)
