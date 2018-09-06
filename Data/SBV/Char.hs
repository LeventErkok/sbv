-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Char
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
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

{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings   #-}

module Data.SBV.Char (
        -- * Occurrence in a string
        elem, notElem
        -- * Conversion to\/from 'SInteger'
        , ord, chr
        -- * Conversion to upper\/lower case
        , toLower, toUpper
        -- * Converting digits to ints and back
        , digitToInt, intToDigit
        -- * Character classification
        , isControl, isSpace, isLower, isUpper, isAlpha, isAlphaNum, isPrint, isDigit, isOctDigit, isHexDigit, isLetter, isMark, isNumber, isPunctuation, isSymbol, isSeparator
        -- * Subranges
        , isAscii, isLatin1, isAsciiLetter, isAsciiUpper, isAsciiLower
        ) where

import Prelude hiding (elem, notElem)
import qualified Prelude as P

import Data.SBV.Core.Data
import Data.SBV.Core.Model
import Data.SBV.Utils.Boolean

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
-- >>> prove $ \c -> bnot (c `elem` "")
-- Q.E.D.
elem :: SChar -> SString -> SBool
c `elem` s
 | Just cs <- unliteral s, Just cc <- unliteral c
 = literal (cc `P.elem` cs)
 | Just cs <- unliteral s                            -- If only the second string is concrete, element-wise checking is still much better!
 = bAny (c .==) $ map literal cs
 | True
 = singleton c `isInfixOf` s

-- | Is the character not in the string?
--
-- >>> prove $ \c s -> c `elem` s <=> bnot (c `notElem` s)
-- Q.E.D.
notElem :: SChar -> SString -> SBool
c `notElem` s = bnot (c `elem` s)

-- | The 'ord' of a character.
ord :: SChar -> SInteger
ord c
 | Just cc <- unliteral c
 = literal (fromIntegral (C.ord cc))
 | True
 = SBV $ SVal kTo $ Right $ cache r
 where kFrom = KBounded False 8
       kTo   = KUnbounded
       r st = do csw <- sbvToSW st c
                 newExpr st kTo (SBVApp (KindCast kFrom kTo) [csw])

-- | Conversion from an integer to a character.
--
-- >>> prove $ \x -> 0 .<= x &&& x .< 256 ==> ord (chr x) .== x
-- Q.E.D.
-- >>> prove $ \x -> chr (ord x) .== x
-- Q.E.D.
chr :: SInteger -> SChar
chr w
 | Just cw <- unliteral w
 = literal (C.chr (fromIntegral cw))
 | True
 = SBV $ SVal KChar $ Right $ cache r
 where w8 :: SWord8
       w8 = sFromIntegral w
       r st = do SW _ n <- sbvToSW st w8
                 return $ SW KChar n

-- | Convert to lower-case.
--
-- >>> prove $ \c -> toLower (toLower c) .== toLower c
-- Q.E.D.
-- >>> prove $ \c -> isLower c ==> toLower (toUpper c) .== c
-- Q.E.D.
toLower :: SChar -> SChar
toLower c = ite (isUpper c) (chr (ord c + 32)) c

-- | Convert to upper-case. N.B. There are three special cases!
--
--   * The character \223 is special. It corresponds to the German Eszett, it is considered lower-case,
--     and furthermore it's upper-case maps back to itself within our character-set. So, we leave it
--     untouched.
--
--   * The character \181 maps to upper-case \924, which is beyond our character set. We leave it
--     untouched. (This is the A with an acute accent.)
--
--   * The character \255 maps to upper-case \376, which is beyond our character set. We leave it
--     untouched. (This is the non-breaking space character.)
--
-- >>> prove $ \c -> toUpper (toUpper c) .== toUpper c
-- Q.E.D.
-- >>> prove $ \c -> isUpper c ==> toUpper (toLower c) .== c
-- Q.E.D.
toUpper :: SChar -> SChar
toUpper c = ite (isLower c &&& c `notElem` "\181\223\255") (chr (ord c - 32)) c

-- | Convert a digit to an integer. Works for hexadecimal digits too. If the input isn't a digit,
-- then return -1.
--
-- >>> prove $ \c -> isDigit c ||| isHexDigit c ==> digitToInt c .>= 0 &&& digitToInt c .<= 15
-- Q.E.D.
-- >>> prove $ \c -> bnot (isDigit c ||| isHexDigit c) ==> digitToInt c .== -1
-- Q.E.D.
digitToInt :: SChar -> SInteger
digitToInt c = ite (uc `elem` "0123456789") (sFromIntegral (o - ord (literal '0')))
             $ ite (uc `elem` "ABCDEF")     (sFromIntegral (o - ord (literal 'A') + 10))
             $ -1
  where uc = toUpper c
        o  = ord uc

-- | Convert an an integer to a digit, inverse of 'digitToInt'. If the integer is out of
-- bounds, we return the arbitrarily chosen space character. Note that for hexadecimal
-- letters, we return the corresponding lowercase letter.
--
-- >>> prove $ \i -> i .>= 0 &&& i .<= 15 ==> digitToInt (intToDigit i) .== i
-- Q.E.D.
-- >>> prove $ \i -> i .<  0 ||| i .>  15 ==> digitToInt (intToDigit i) .== -1
-- Q.E.D.
-- >>> prove $ \c -> digitToInt c .== -1 <=> intToDigit (digitToInt c) .== literal ' '
-- Q.E.D.
intToDigit :: SInteger -> SChar
intToDigit i = ite (i .>=  0 &&& i .<=  9) (chr (sFromIntegral i + ord (literal '0')))
             $ ite (i .>= 10 &&& i .<= 15) (chr (sFromIntegral i + ord (literal 'a') - 10))
             $ literal ' '

-- | Is this a control character? Control characters are essentially the non-printing characters.
isControl :: SChar -> SBool
isControl = (`elem` controls)
  where controls = "\NUL\SOH\STX\ETX\EOT\ENQ\ACK\a\b\t\n\v\f\r\SO\SI\DLE\DC1\DC2\DC3\DC4\NAK\SYN\ETB\CAN\EM\SUB\ESC\FS\GS\RS\US\DEL\128\129\130\131\132\133\134\135\136\137\138\139\140\141\142\143\144\145\146\147\148\149\150\151\152\153\154\155\156\157\158\159"

-- | Is this white-space? That is, one of "\t\n\v\f\r \160".
isSpace :: SChar -> SBool
isSpace = (`elem` spaces)
  where spaces = "\t\n\v\f\r \160"

-- | Is this a lower-case character?
--
-- >>> prove $ \c -> isUpper c ==> isLower (toLower c)
-- Q.E.D.
isLower :: SChar -> SBool
isLower = (`elem` lower)
  where lower = "abcdefghijklmnopqrstuvwxyz\181\223\224\225\226\227\228\229\230\231\232\233\234\235\236\237\238\239\240\241\242\243\244\245\246\248\249\250\251\252\253\254\255"

-- | Is this an upper-case character?
--
-- >>> prove $ \c -> bnot (isLower c &&& isUpper c)
-- Q.E.D.
isUpper :: SChar -> SBool
isUpper = (`elem` upper)
  where upper = "ABCDEFGHIJKLMNOPQRSTUVWXYZ\192\193\194\195\196\197\198\199\200\201\202\203\204\205\206\207\208\209\210\211\212\213\214\216\217\218\219\220\221\222"

-- | Is this an alphabet character? That is lower-case, upper-case and title-case letters, plus letters of caseless scripts and modifiers letters.
isAlpha :: SChar -> SBool
isAlpha = (`elem` alpha)
  where alpha = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz\170\181\186\192\193\194\195\196\197\198\199\200\201\202\203\204\205\206\207\208\209\210\211\212\213\214\216\217\218\219\220\221\222\223\224\225\226\227\228\229\230\231\232\233\234\235\236\237\238\239\240\241\242\243\244\245\246\248\249\250\251\252\253\254\255"

-- | Is this an 'isAlpha' or 'isNumber'.
--
-- >>> prove $ \c -> isAlphaNum c <=> isAlpha c ||| isNumber c
-- Q.E.D.
isAlphaNum :: SChar -> SBool
isAlphaNum c = isAlpha c ||| isNumber c

-- | Is this a printable character? Essentially the complement of 'isControl', with one
-- exception. The Latin-1 character \173 is neither control nor printable. Go figure.
--
-- >>> prove $ \c -> c .== literal '\173' ||| isControl c <=> bnot (isPrint c)
-- Q.E.D.
isPrint :: SChar -> SBool
isPrint c = c ./= literal '\173' &&& bnot (isControl c)

-- | Is this an ASCII digit, i.e., one of @0@..@9@. Note that this is a subset of 'isNumber'
--
-- >>> prove $ \c -> isDigit c ==> isNumber c
-- Q.E.D.
isDigit :: SChar -> SBool
isDigit = (`elem` "0123456789")

-- | Is this an Octal digit, i.e., one of @0@..@7@.
--
-- >>> prove $ \c -> isOctDigit c ==> isDigit c
-- Q.E.D.
isOctDigit :: SChar -> SBool
isOctDigit = (`elem` "01234567")

-- | Is this a Hex digit, i.e, one of @0@..@9@, @a@..@f@, @A@..@F@.
--
-- >>> prove $ \c -> isHexDigit c ==> isAlphaNum c
-- Q.E.D.
isHexDigit :: SChar -> SBool
isHexDigit = (`elem` "0123456789abcdefABCDEF")

-- | Is this an alphabet character. Note that this function is equivalent to 'isAlpha'.
--
-- >>> prove $ \c -> isLetter c <=> isAlpha c
-- Q.E.D.
isLetter :: SChar -> SBool
isLetter = isAlpha

-- | Is this a mark? Note that the Latin-1 subset doesn't have any marks; so this function
-- is simply constant false for the time being.
--
-- >>> prove $ bnot . isMark
-- Q.E.D.
isMark :: SChar -> SBool
isMark = const false

-- | Is this a number character? Note that this set contains not only the digits, but also
-- the codes for a few numeric looking characters like 1/2 etc. Use 'isDigit' for the digits @0@ through @9@.
isNumber :: SChar -> SBool
isNumber = (`elem` "0123456789\178\179\185\188\189\190")

-- | Is this a punctuation mark?
isPunctuation :: SChar -> SBool
isPunctuation = (`elem` "!\"#%&'()*,-./:;?@[\\]_{}\161\167\171\182\183\187\191")

-- | Is this a symbol?
isSymbol :: SChar -> SBool
isSymbol = (`elem` "$+<=>^`|~\162\163\164\165\166\168\169\172\174\175\176\177\180\184\215\247")

-- | Is this a separator?
--
-- >>> prove $ \c -> isSeparator c ==> isSpace c
-- Q.E.D.
isSeparator :: SChar -> SBool
isSeparator = (`elem` " \160")

-- | Is this an ASCII character, i.e., the first 128 characters.
isAscii :: SChar -> SBool
isAscii c = ord c .< 128

-- | Is this a Latin1 character? Note that this function is always true since 'SChar' corresponds
-- precisely to Latin1 for the time being.
--
-- >>> prove isLatin1
-- Q.E.D.
isLatin1 :: SChar -> SBool
isLatin1 = const true

-- | Is this an ASCII letter?
--
-- >>> prove $ \c -> isAsciiLetter c <=> isAsciiUpper c ||| isAsciiLower c
-- Q.E.D.
isAsciiLetter :: SChar -> SBool
isAsciiLetter c = isAsciiUpper c ||| isAsciiLower c

-- | Is this an ASCII Upper-case letter? i.e., @A@ thru @Z@
--
-- >>> prove $ \c -> isAsciiUpper c <=> ord c .>= ord (literal 'A') &&& ord c .<= ord (literal 'Z')
-- Q.E.D.
-- >>> prove $ \c -> isAsciiUpper c <=> isAscii c &&& isUpper c
-- Q.E.D.
isAsciiUpper :: SChar -> SBool
isAsciiUpper = (`elem` literal ['A' .. 'Z'])

-- | Is this an ASCII Lower-case letter? i.e., @a@ thru @z@
--
-- >>> prove $ \c -> isAsciiLower c <=> ord c .>= ord (literal 'a') &&& ord c .<= ord (literal 'z')
-- Q.E.D.
-- >>> prove $ \c -> isAsciiLower c <=> isAscii c &&& isLower c
-- Q.E.D.
isAsciiLower :: SChar -> SBool
isAsciiLower = (`elem` literal ['a' .. 'z'])
