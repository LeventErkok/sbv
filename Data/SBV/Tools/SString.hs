{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Tools.SString
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- A collection of string/character utilities, useful when working
-- with symbolic strings. To the extent possible, the functions
-- in this module follow those of "Data.List" and "Data.Char",  so
-- importing qualified is the recommended workflow.
-----------------------------------------------------------------------------

module Data.SBV.Tools.SString (
        -- * The symbolic "character"
        SChar
        -- * Conversion to/from SWord8
        , ord, chr
        -- * Deconstructing/Reconstructing
        , head, tail, charToStr, strToCharAt, implode
        -- * Membership
        , elem
        -- * Length
        , length
        -- * Substrings
        , take, drop
        -- * Recognizers
        , isControl, isPrint, isSpace, isLower, isUpper, isAlpha, isAlphaNum, isDigit, isOctDigit, isHexDigit, isLetter, isPunctuation
        -- * Regular Expressions
        -- ** White space
        , reNewline, reWhitespace, reWhiteSpaceNoNewLine
        -- ** Separators
        , reTab, rePunctuation
        -- ** Digits
        , reDigit, reOctDigit, reHexDigit
        -- ** Numbers
        , reDecimal, reOctal, reHexadecimal
        -- ** Identifiers
        , reIdentifier
        ) where

import Prelude hiding (elem, head, tail, length, take, drop)
import qualified Prelude as P

import Data.SBV.Core.Data
import Data.SBV.Core.Model
import Data.SBV.Core.String
import Data.SBV.Utils.Boolean (bnot)

import qualified Data.Char as C
import Data.List (genericLength, genericIndex)

-- For doctest use only
--
-- $setup
-- >>> import Data.SBV.Provers.Prover (prove)
-- >>> import Data.SBV.Utils.Boolean  ((&&&), (==>), (<=>))

-- | The symbolic "character." Note that, as far as SBV's symbolic strings are concerned, a character
-- is essentially an 8-bit unsigned value, and hence is equivalent to the type 'SWord8'. Technically
-- speaking, this corresponds to the ISO-8859-1 (Latin-1) character set. A Haskell 'Char', on the other
-- hand, is a unicode beast; so there isn't a 1-1 correspondence between a Haskell character and an
-- SBV character. This limitation is due to the SMT-solvers only supporting this particular subset,
-- which may be relaxed in future versions.
type SChar = SWord8

-- | The 'ord' of a character. Note that this is essentially identity function due to
-- our representation, appropriately typed to have any numeric type.
ord :: SIntegral a => SChar -> SBV a
ord = sFromIntegral

-- | Conversion from a value to a character. If the value is not in the range
-- 0..255, then the output is underspecified.
--
-- >>> prove $ \x -> (0 .<= x &&& x .< (255 :: SInteger)) ==> ord (chr x) .== x
-- Q.E.D.
-- >>> prove $ \x -> chr ((ord x) :: SInteger) .== x
-- Q.E.D.
chr :: SIntegral a => SBV a -> SChar
chr = sFromIntegral

-- | @`head`@ returns the head of a string. Unspecified if the string is empty.
--
-- >>> prove $ \c -> head (charToStr c) .== c
-- Q.E.D.
head :: SString -> SWord8
head = (`strToCharAt` 0)

-- | @`tail`@ returns the tail of a string. Unspecified if the string is empty.
--
-- >>> prove $ \h s -> tail (charToStr h .++ s) .== s
-- Q.E.D.
-- >>> prove $ \s -> length s .> 0 ==> length (tail s) .== length s - 1
-- Q.E.D.
-- >>> prove $ \s -> bnot (strNull s) ==> charToStr (head s) .++ tail s .== s
-- Q.E.D.
tail :: SString -> SString
tail s
 | Just (_:cs) <- unliteral s
 = literal cs
 | True
 = strSubstr s 1 (length s - 1)


-- | @`charToStr` c@ is the string of length 1 that contains the only character
-- whose value is the 8-bit value @c@.
--
-- >>> :set -XOverloadedStrings
-- >>> prove $ \c -> c .== 65 ==> charToStr c .== "A"
-- Q.E.D.
-- >>> prove $ \c -> length (charToStr c) .== 1
-- Q.E.D.
charToStr :: SWord8 -> SString
charToStr = lift1 StrUnit (Just $ \cv -> [C.chr (fromIntegral cv)])

-- | @`strToCharAt` s i@ is the 8-bit value stored at location @i@. Unspecified if
-- index is out of bounds.
--
-- >>> :set -XOverloadedStrings
-- >>> prove $ \i -> i .>= 0 &&& i .<= 4 ==> "AAAAA" `strToCharAt` i .== 65
-- Q.E.D.
-- >>> prove $ \s i c -> s `strToCharAt` i .== c ==> strIndexOf s (charToStr c) .<= i
-- Q.E.D.
strToCharAt :: SString -> SInteger -> SWord8
strToCharAt s i
  | Just cs <- unliteral s, Just ci <- unliteral i, ci >= 0, ci < genericLength cs, let c = C.ord (cs `genericIndex` ci), c >= 0, c < 256
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

-- | @`implode` cs@ is the string of length @|cs|@ containing precisely those
-- characters. Note that there is no corresponding function @explode@, since
-- we wouldn't know the length of a symbolic string.
--
-- >>> prove $ \c1 c2 c3 -> length (implode [c1, c2, c3]) .== 3
-- Q.E.D.
-- >>> prove $ \c1 c2 c3 -> map (strToCharAt (implode [c1, c2, c3])) (map literal [0 .. 2]) .== [c1, c2, c3]
-- Q.E.D.
implode :: [SChar] -> SString
implode = foldr ((.++) . charToStr) ""

-- | Is the character in the literal string? Used internally.
--
-- >>> prove $ \c -> c `elem` charToStr c
-- Q.E.D.
-- >>> :set -XOverloadedStrings
-- >>> prove $ \c -> bnot (c `elem` "")
-- Q.E.D.
elem :: SChar -> SString -> SBool
elem c s = charToStr c `strIsInfixOf` s

-- | Length of a string.
--
-- >>> sat $ \s -> length s .== 2
-- Satisfiable. Model:
--   s0 = "\NUL\NUL" :: String
-- >>> sat $ \s -> length s .< 0
-- Unsatisfiable
-- >>> prove $ \s1 s2 -> length s1 + length s2 .== length (s1 .++ s2)
-- Q.E.D.
length :: SString -> SInteger
length = lift1 StrLen (Just (fromIntegral . P.length))

-- | @`take` len s@. Corresponds to Haskell's `take` on symbolic-strings.
--
-- >>> prove $ \s i -> i .>= 0 ==> length (take i s) .<= i
-- Q.E.D.
take :: SInteger -> SString -> SString
take i s = ite (i .<= 0)        (literal "")
         $ ite (i .>= length s) s
         $ strSubstr s 0 i

-- | @`drop` len s@. Corresponds to Haskell's `drop` on symbolic-strings.
--
-- >>> prove $ \s i -> length (drop i s) .<= length s
-- Q.E.D.
-- >>> prove $ \s i -> take i s .++ drop i s .== s
-- Q.E.D.
drop :: SInteger -> SString -> SString
drop i s = ite (i .>= ls) (literal "")
         $ ite (i .<= 0)  s
         $ strSubstr s i (ls - i)
  where ls = length s


-- | Selects control characters, which are the non-printing characters.
--
-- >>> prove $ \c -> isControl c <=> bnot (isPrint c)
-- Q.E.D.
isControl :: SChar -> SBool
isControl = (`elem` controls)
  where controls = "\NUL\SOH\STX\ETX\EOT\ENQ\ACK\a\b\t\n\v\f\r\SO\SI\DLE\DC1\DC2\DC3\DC4\NAK\SYN\ETB\CAN\EM\SUB\ESC\FS\GS\RS\US\DEL\128\129\130\131\132\133\134\135\136\137\138\139\140\141\142\143\144\145\146\147\148\149\150\151\152\153\154\155\156\157\158\159"

-- | Selects printable characters. Complement of 'isControl'.
isPrint :: SChar -> SBool
isPrint = bnot . isControl

isSpace               :: a
isSpace               = error "isSpace"

isLower               :: a
isLower               = error "isLower"

isUpper               :: a
isUpper               = error "isUpper"

isAlpha               :: a
isAlpha               = error "isAlpha"

isAlphaNum            :: a
isAlphaNum            = error "isAlphaNum"

isDigit               :: a
isDigit               = error "isDigit"

isOctDigit            :: a
isOctDigit            = error "isOctDigit"

isHexDigit            :: a
isHexDigit            = error "isHexDigit"

isLetter              :: a
isLetter              = error "isLetter"

isPunctuation         :: a
isPunctuation         = error "isPunctuation"

reNewline             :: a
reNewline             = error "reNewline"

reWhitespace          :: a
reWhitespace          = error "reWhitespace"

reWhiteSpaceNoNewLine :: a
reWhiteSpaceNoNewLine = error "reWhiteSpaceNoNewLine"

reTab                 :: a
reTab                 = error "reTab"

rePunctuation         :: a
rePunctuation         = error "rePunctuation"

reDigit               :: a
reDigit               = error "reDigit"

reOctDigit            :: a
reOctDigit            = error "reOctDigit"

reHexDigit            :: a
reHexDigit            = error "reHexDigit"

reDecimal             :: a
reDecimal             = error "reDecimal"

reOctal               :: a
reOctal               = error "reOctal"

reHexadecimal         :: a
reHexadecimal         = error "reHexadecimal"

reIdentifier          :: a
reIdentifier          = error "reIdentifier"

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

-- | Concrete evaluation for unary ops
concEval1 :: (SymWord a, SymWord b) => Maybe (a -> b) -> SBV a -> Maybe (SBV b)
concEval1 mbOp a = literal <$> (mbOp <*> unliteral a)
