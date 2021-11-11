-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Char
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A collection of character utilities, follows the namings
-- in "Data.Char" and is intended to be imported qualified.
-- Also, it is recommended you use the @OverloadedStrings@
-- extension to allow literal strings to be used as
-- symbolic-strings when working with symbolic characters
-- and strings.
--
-- 'SChar' type only covers all unicode characters, following the specification
-- in <http://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml>.
-- However, some of the recognizers only support the Latin1 subset, suffixed
-- by @L1@. The reason for this is that there is no performant way of performing
-- these functions for the entire unicode set. As SMTLib's capabilities increase,
-- we will provide full unicode versions as well.
-----------------------------------------------------------------------------

{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Char (
        -- * Occurrence in a string
        elem, notElem
        -- * Conversion to\/from 'SInteger'
        , ord, chr
        -- * Conversion to upper\/lower case
        , toLowerL1, toUpperL1
        -- * Converting digits to ints and back
        , digitToInt, intToDigit
        -- * Character classification
        , isControlL1, isSpaceL1, isLowerL1, isUpperL1, isAlphaL1, isAlphaNumL1, isPrintL1, isDigit, isOctDigit, isHexDigit
        , isLetterL1, isMarkL1, isNumberL1, isPunctuationL1, isSymbolL1, isSeparatorL1
        -- * Subranges
        , isAscii, isLatin1, isAsciiUpper, isAsciiLower
        ) where

import Prelude hiding (elem, notElem)
import qualified Prelude as P

import Data.SBV.Core.Data
import Data.SBV.Core.Model

import qualified Data.Char as C

import Data.SBV.String (isInfixOf, singleton)

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV
-- >>> import Data.SBV.String (isInfixOf, singleton)
-- >>> import Prelude hiding(elem, notElem)
-- >>> :set -XOverloadedStrings

-- | Is the character in the string?
--
-- >>> :set -XOverloadedStrings
-- >>> prove $ \c -> c `elem` singleton c
-- Q.E.D.
-- >>> prove $ \c -> sNot (c `elem` "")
-- Q.E.D.
elem :: SChar -> SString -> SBool
c `elem` s
 | Just cs <- unliteral s, Just cc <- unliteral c
 = literal (cc `P.elem` cs)
 | Just cs <- unliteral s                            -- If only the second string is concrete, element-wise checking is still much better!
 = sAny (c .==) $ map literal cs
 | True
 = singleton c `isInfixOf` s

-- | Is the character not in the string?
--
-- >>> prove $ \c s -> c `elem` s .<=> sNot (c `notElem` s)
-- Q.E.D.
notElem :: SChar -> SString -> SBool
c `notElem` s = sNot (c `elem` s)

-- | The 'ord' of a character.
ord :: SChar -> SInteger
ord c
 | Just cc <- unliteral c
 = literal (fromIntegral (C.ord cc))
 | True
 = SBV $ SVal KUnbounded $ Right $ cache r
 where r st = do csv <- sbvToSV st c
                 newExpr st KUnbounded (SBVApp (StrOp StrToCode) [csv])

-- | Conversion from an integer to a character.
--
-- >>> prove $ \x -> 0 .<= x .&& x .< 256 .=> ord (chr x) .== x
-- Q.E.D.
-- >>> prove $ \x -> chr (ord x) .== x
-- Q.E.D.
chr :: SInteger -> SChar
chr w
 | Just cw <- unliteral w
 = literal (C.chr (fromIntegral cw))
 | True
 = SBV $ SVal KChar $ Right $ cache r
 where r st = do wsv <- sbvToSV st w
                 newExpr st KChar (SBVApp (StrOp StrFromCode) [wsv])

-- | Lift a char function to a symbolic version. If the given char is
-- not in the class recognized by predicate, the output is the same as the input.
-- Only works for the Latin1 set, i.e., the first 256 characters. If the given
-- character is outside this range, it's returned unchanged.
liftFunL1 :: (Char -> Char) -> SChar -> SChar
liftFunL1 f c = walk kernel
  where kernel = [g | g <- map C.chr [0 .. 255], g /= f g]
        walk []     = c
        walk (d:ds) = ite (literal d .== c) (literal (f d)) (walk ds)

-- | Lift a char predicate to a symbolic version. Only works for the Latin1 set, i.e., the
-- first 256 characters.
liftPredL1 :: (Char -> Bool) -> SChar -> SBool
liftPredL1 predicate c = c `sElem` [literal g | g <- map C.chr [0 .. 255], predicate g]

-- | Convert to lower-case. Only works for the Latin1 subset, otherwise returns its argument unchanged.
--
-- >>> prove $ \c -> toLowerL1 (toLowerL1 c) .== toLowerL1 c
-- Q.E.D.
-- >>> prove $ \c -> isLowerL1 c .&& c `notElem` "\181\255" .=> toLowerL1 (toUpperL1 c) .== c
-- Q.E.D.
toLowerL1 :: SChar -> SChar
toLowerL1 = liftFunL1 C.toLower

-- | Convert to upper-case. Only works for the Latin1 subset, otherwise returns its argument unchanged.
--
-- >>> prove $ \c -> toUpperL1 (toUpperL1 c) .== toUpperL1 c
-- Q.E.D.
-- >>> prove $ \c -> isUpperL1 c .=> toUpperL1 (toLowerL1 c) .== c
-- Q.E.D.
toUpperL1 :: SChar -> SChar
toUpperL1 = liftFunL1 C.toUpper

-- | Convert a digit to an integer. Works for hexadecimal digits too. If the input isn't a digit,
-- then return -1.
--
-- >>> prove $ \c -> isDigit c .|| isHexDigit c .=> digitToInt c .>= 0 .&& digitToInt c .<= 15
-- Q.E.D.
-- >>> prove $ \c -> sNot (isDigit c .|| isHexDigit c) .=> digitToInt c .== -1
-- Q.E.D.
digitToInt :: SChar -> SInteger
digitToInt c = ite (uc `elem` "0123456789") (sFromIntegral (o - ord (literal '0')))
             $ ite (uc `elem` "ABCDEF")     (sFromIntegral (o - ord (literal 'A') + 10))
             $ -1
  where uc = toUpperL1 c
        o  = ord uc

-- | Convert an integer to a digit, inverse of 'digitToInt'. If the integer is out of
-- bounds, we return the arbitrarily chosen space character. Note that for hexadecimal
-- letters, we return the corresponding lowercase letter.
--
-- >>> prove $ \i -> i .>= 0 .&& i .<= 15 .=> digitToInt (intToDigit i) .== i
-- Q.E.D.
-- >>> prove $ \i -> i .<  0 .|| i .>  15 .=> digitToInt (intToDigit i) .== -1
-- Q.E.D.
-- >>> prove $ \c -> digitToInt c .== -1 .<=> intToDigit (digitToInt c) .== literal ' '
-- Q.E.D.
intToDigit :: SInteger -> SChar
intToDigit i = ite (i .>=  0 .&& i .<=  9) (chr (sFromIntegral i + ord (literal '0')))
             $ ite (i .>= 10 .&& i .<= 15) (chr (sFromIntegral i + ord (literal 'a') - 10))
             $ literal ' '

-- | Is this a control character? Control characters are essentially the non-printing characters. Only works for the Latin1 subset, otherwise returns 'sFalse'.
isControlL1 :: SChar -> SBool
isControlL1 = liftPredL1 C.isControl

-- | Is this white-space? Only works for the Latin1 subset, otherwise returns 'sFalse'.
isSpaceL1 :: SChar -> SBool
isSpaceL1 = liftPredL1 C.isSpace

-- | Is this a lower-case character? Only works for the Latin1 subset, otherwise returns 'sFalse'.
--
-- >>> prove $ \c -> isUpperL1 c .=> isLowerL1 (toLowerL1 c)
-- Q.E.D.
isLowerL1 :: SChar -> SBool
isLowerL1 = liftPredL1 C.isLower

-- | Is this an upper-case character? Only works for the Latin1 subset, otherwise returns 'sFalse'.
--
-- >>> prove $ \c -> sNot (isLowerL1 c .&& isUpperL1 c)
-- Q.E.D.
isUpperL1 :: SChar -> SBool
isUpperL1 = liftPredL1 C.isUpper

-- | Is this an alphabet character? That is lower-case, upper-case and title-case letters, plus letters of caseless scripts and modifiers letters.
-- Only works for the Latin1 subset, otherwise returns 'sFalse'.
isAlphaL1 :: SChar -> SBool
isAlphaL1 = liftPredL1 C.isAlpha

-- | Is this an alphabetical character or a digit? Only works for the Latin1 subset, otherwise returns 'sFalse'.
--
-- >>> prove $ \c -> isAlphaNumL1 c .<=> isAlphaL1 c .|| isNumberL1 c
-- Q.E.D.
isAlphaNumL1 :: SChar -> SBool
isAlphaNumL1 = liftPredL1 C.isAlphaNum

-- | Is this a printable character? Only works for the Latin1 subset, otherwise returns 'sFalse'.
isPrintL1 :: SChar -> SBool
isPrintL1 = liftPredL1 C.isPrint

-- | Is this an ASCII digit, i.e., one of @0@..@9@. Note that this is a subset of 'isNumberL1' 
--
-- >>> prove $ \c -> isDigit c .=> isNumberL1 c
-- Q.E.D.
isDigit :: SChar -> SBool
isDigit = liftPredL1 C.isDigit

-- | Is this an Octal digit, i.e., one of @0@..@7@.
isOctDigit :: SChar -> SBool
isOctDigit = liftPredL1 C.isOctDigit

-- | Is this a Hex digit, i.e, one of @0@..@9@, @a@..@f@, @A@..@F@.
--
-- >>> prove $ \c -> isHexDigit c .=> isAlphaNumL1 c
-- Q.E.D.
isHexDigit :: SChar -> SBool
isHexDigit = liftPredL1 C.isHexDigit

-- | Is this an alphabet character. Only works for the Latin1 subset, otherwise returns 'sFalse'.
--
-- >>> prove $ \c -> isLetterL1 c .<=> isAlphaL1 c
-- Q.E.D.
isLetterL1 :: SChar -> SBool
isLetterL1 = liftPredL1 C.isLetter

-- | Is this a mark? Only works for the Latin1 subset, otherwise returns 'sFalse'.
--
-- Note that there are no marks in the Latin1 set, so this function always returns false!
--
-- >>> prove $ sNot . isMarkL1
-- Q.E.D.
isMarkL1 :: SChar -> SBool
isMarkL1 = liftPredL1 C.isMark

-- | Is this a number character? Only works for the Latin1 subset, otherwise returns 'sFalse'.
isNumberL1 :: SChar -> SBool
isNumberL1 = liftPredL1 C.isNumber

-- | Is this a punctuation mark? Only works for the Latin1 subset, otherwise returns 'sFalse'.
isPunctuationL1 :: SChar -> SBool
isPunctuationL1 = liftPredL1 C.isPunctuation

-- | Is this a symbol? Only works for the Latin1 subset, otherwise returns 'sFalse'.
isSymbolL1 :: SChar -> SBool
isSymbolL1 = liftPredL1 C.isSymbol

-- | Is this a separator? Only works for the Latin1 subset, otherwise returns 'sFalse'.
--
-- >>> prove $ \c -> isSeparatorL1 c .=> isSpaceL1 c
-- Q.E.D.
isSeparatorL1 :: SChar -> SBool
isSeparatorL1 = liftPredL1 C.isSeparator

-- | Is this an ASCII character, i.e., the first 128 characters.
isAscii :: SChar -> SBool
isAscii c = ord c .< 128

-- | Is this a Latin1 character?
isLatin1 :: SChar -> SBool
isLatin1 c = ord c .< 256

-- | Is this an ASCII Upper-case letter? i.e., @A@ thru @Z@
--
-- >>> prove $ \c -> isAsciiUpper c .<=> ord c .>= ord (literal 'A') .&& ord c .<= ord (literal 'Z')
-- Q.E.D.
-- >>> prove $ \c -> isAsciiUpper c .<=> isAscii c .&& isUpperL1 c
-- Q.E.D.
isAsciiUpper :: SChar -> SBool
isAsciiUpper = liftPredL1 C.isAsciiUpper

-- | Is this an ASCII Lower-case letter? i.e., @a@ thru @z@
--
-- >>> prove $ \c -> isAsciiLower c .<=> ord c .>= ord (literal 'a') .&& ord c .<= ord (literal 'z')
-- Q.E.D.
-- >>> prove $ \c -> isAsciiLower c .<=> isAscii c .&& isLowerL1 c
-- Q.E.D.
isAsciiLower :: SChar -> SBool
isAsciiLower = liftPredL1 C.isAsciiLower
