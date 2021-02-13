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
-- Note that currently 'SChar' type only covers Latin1 (i.e., the first 256
-- characters), as opposed to Haskell's Unicode character support. However,
-- there is a pending SMTLib proposal to extend this set to Unicode, at
-- which point we will update these functions to match the implementations.
-- For details, see: <http://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml>
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
        , toLower, toUpper, toTitle
        -- * Converting digits to ints and back
        , digitToInt, intToDigit
        -- * Character classification
        , isControl, isSpace, isLower, isUpper, isAlpha, isAlphaNum, isPrint, isDigit, isOctDigit, isHexDigit, isLetter, isMark, isNumber, isPunctuation, isSymbol, isSeparator
        -- * Subranges
        , isAscii, isLatin1, isAsciiUpper, isAsciiLower
        ) where

import Prelude hiding (elem, notElem)
import qualified Prelude as P

import Data.SBV.Core.Data
import Data.SBV.Core.Model

import qualified Data.Char as C

import Data.SBV.String (isInfixOf, singleton)

-- For doctest use only
--
-- $setup
-- >>> import Data.SBV.Provers.Prover (prove, sat)
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
liftFun :: (Char -> Char) -> SChar -> SChar
liftFun f c = walk kernel
  where kernel = [g | g <- [minBound .. maxBound :: Char], g /= f g]
        walk []     = c
        walk (d:ds) = ite (literal d .== c) (literal (f d)) (walk ds)

-- | Lift a char predicate to a symbolic version.
liftPred :: (Char -> Bool) -> SChar -> SBool
liftPred predicate c = c `sElem` [literal g | g <- [minBound .. maxBound :: Char], predicate g]

-- | Convert to lower-case.
--
-- >>> prove $ \c -> toLower (toLower c) .== toLower c
-- Q.E.D.
-- >>> prove $ \c -> isLower c .=> toLower (toUpper c) .== c
-- Q.E.D.
toLower :: SChar -> SChar
toLower = liftFun C.toUpper

-- | Convert to upper-case.
--
-- >>> prove $ \c -> toUpper (toUpper c) .== toUpper c
-- Q.E.D.
-- >>> prove $ \c -> isUpper c .=> toUpper (toLower c) .== c
-- Q.E.D.
toUpper :: SChar -> SChar
toUpper = liftFun C.toLower

-- | Convert to title-case.
toTitle :: SChar -> SChar
toTitle = liftFun C.toTitle

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
  where uc = toUpper c
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

-- | Is this a control character? Control characters are essentially the non-printing characters.
isControl :: SChar -> SBool
isControl = liftPred C.isControl

-- | Is this white-space? That is, one of "\t\n\v\f\r \160".
isSpace :: SChar -> SBool
isSpace = liftPred C.isSpace

-- | Is this a lower-case character?
--
-- >>> prove $ \c -> isUpper c .=> isLower (toLower c)
-- Q.E.D.
isLower :: SChar -> SBool
isLower = liftPred C.isLower

-- | Is this an upper-case character?
--
-- >>> prove $ \c -> sNot (isLower c .&& isUpper c)
-- Q.E.D.
isUpper :: SChar -> SBool
isUpper = liftPred C.isUpper

-- | Is this an alphabet character? That is lower-case, upper-case and title-case letters, plus letters of caseless scripts and modifiers letters.
isAlpha :: SChar -> SBool
isAlpha = liftPred C.isAlpha

-- | Is this an 'isAlpha' or 'isNumber'.
--
-- >>> prove $ \c -> isAlphaNum c .<=> isAlpha c .|| isNumber c
-- Q.E.D.
isAlphaNum :: SChar -> SBool
isAlphaNum = liftPred C.isAlphaNum

-- | Is this a printable character?
isPrint :: SChar -> SBool
isPrint = liftPred C.isPrint

-- | Is this an ASCII digit, i.e., one of @0@..@9@. Note that this is a subset of 'isNumber'
--
-- >>> prove $ \c -> isDigit c .=> isNumber c
-- Q.E.D.
isDigit :: SChar -> SBool
isDigit = liftPred C.isDigit

-- | Is this an Octal digit, i.e., one of @0@..@7@.
--
-- >>> prove $ \c -> isOctDigit c .=> isDigit c
-- Q.E.D.
isOctDigit :: SChar -> SBool
isOctDigit = liftPred C.isOctDigit

-- | Is this a Hex digit, i.e, one of @0@..@9@, @a@..@f@, @A@..@F@.
--
-- >>> prove $ \c -> isHexDigit c .=> isAlphaNum c
-- Q.E.D.
isHexDigit :: SChar -> SBool
isHexDigit = liftPred C.isHexDigit

-- | Is this an alphabet character. Note that this function is equivalent to 'isAlpha'.
--
-- >>> prove $ \c -> isLetter c .<=> isAlpha c
-- Q.E.D.
isLetter :: SChar -> SBool
isLetter = liftPred C.isLetter

-- | Is this a mark?
isMark :: SChar -> SBool
isMark = liftPred C.isMark

-- | Is this a number character?
isNumber :: SChar -> SBool
isNumber = liftPred C.isNumber

-- | Is this a punctuation mark?
isPunctuation :: SChar -> SBool
isPunctuation = liftPred C.isPunctuation

-- | Is this a symbol?
isSymbol :: SChar -> SBool
isSymbol = liftPred C.isSymbol

-- | Is this a separator?
--
-- >>> prove $ \c -> isSeparator c .=> isSpace c
-- Q.E.D.
isSeparator :: SChar -> SBool
isSeparator = liftPred C.isSeparator

-- | Is this an ASCII character, i.e., the first 128 characters.
isAscii :: SChar -> SBool
isAscii = liftPred C.isAscii

-- | Is this a Latin1 character?
isLatin1 :: SChar -> SBool
isLatin1 = liftPred C.isLatin1

-- | Is this an ASCII Upper-case letter? i.e., @A@ thru @Z@
--
-- >>> prove $ \c -> isAsciiUpper c .<=> ord c .>= ord (literal 'A') .&& ord c .<= ord (literal 'Z')
-- Q.E.D.
-- >>> prove $ \c -> isAsciiUpper c .<=> isAscii c .&& isUpper c
-- Q.E.D.
isAsciiUpper :: SChar -> SBool
isAsciiUpper = liftPred C.isAsciiUpper

-- | Is this an ASCII Lower-case letter? i.e., @a@ thru @z@
--
-- >>> prove $ \c -> isAsciiLower c .<=> ord c .>= ord (literal 'a') .&& ord c .<= ord (literal 'z')
-- Q.E.D.
-- >>> prove $ \c -> isAsciiLower c .<=> isAscii c .&& isLower c
-- Q.E.D.
isAsciiLower :: SChar -> SBool
isAsciiLower = liftPred C.isAsciiLower
