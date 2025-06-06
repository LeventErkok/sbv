-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.RegExp
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A collection of regular-expression related utilities. The recommended
-- workflow is to import this module qualified as the names of the functions
-- are specifically chosen to be common identifiers. Also, it is recommended
-- you use the @OverloadedStrings@ extension to allow literal strings to be
-- used as symbolic-strings and regular-expressions when working with
-- this module.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.RegExp (
        -- * Regular expressions
        -- $regexpeq
        RegExp(..)
        -- * Matching
        -- $matching
        , RegExpMatchable(..)
        -- * Constructing regular expressions
        -- ** Basics
        , everything, nothing, anyChar
        -- ** Literals
        , exactly
        -- ** A class of characters
        , oneOf
        -- ** Spaces
        , newline, whiteSpaceNoNewLine, whiteSpace
        -- ** Separators
        , tab, punctuation
        -- ** Letters
        , asciiLetter, asciiLower, asciiUpper
        -- ** Digits
        , digit, octDigit, hexDigit
        -- ** Numbers
        , decimal, octal, hexadecimal, floating
        -- ** Identifiers
        , identifier
        ) where

import Prelude hiding (length, take, elem, notElem, head, replicate, filter, map)

import qualified Prelude   as P
import qualified Data.List as L

import Data.SBV.Core.Data

import Data.SBV.List
import qualified Data.Char as C

import Data.Proxy

-- For testing only
import Data.SBV.Char

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV
-- >>> import Data.SBV.Char
-- >>> import Data.SBV.List
-- >>> import Prelude hiding (length, take, elem, notElem, head, map)
-- >>> import qualified Prelude as P
-- >>> :set -XOverloadedStrings
-- >>> :set -XScopedTypeVariables
#endif

-- | Matchable class. Things we can match against a 'RegExp'.
--
-- For instance, you can generate valid-looking phone numbers like this:
--
-- >>> :set -XOverloadedStrings
-- >>> let dig09 = Range '0' '9'
-- >>> let dig19 = Range '1' '9'
-- >>> let pre   = dig19 * Loop 2 2 dig09
-- >>> let post  = dig19 * Loop 3 3 dig09
-- >>> let phone = pre * "-" * post
-- >>> sat $ \(s :: SString) -> s `match` phone
-- Satisfiable. Model:
--   s0 = "800-8000" :: String
class RegExpMatchable a where
   -- | @`match` s r@ checks whether @s@ is in the language generated by @r@.
   match :: a -> RegExp -> SBool

-- | Matching a character simply means the singleton string matches the regex.
instance RegExpMatchable SChar where
   match = match . singleton

-- | Matching symbolic strings.
instance RegExpMatchable SString where
   match input regExp = lift1 (StrInRe regExp) (Just (go regExp P.null)) input
     where -- This isn't super efficient, but it gets the job done.
           go :: RegExp -> (String -> Bool) -> String -> Bool
           go (Literal l)    k s      = l `L.isPrefixOf` s && k (P.drop (P.length l) s)
           go All            _ _      = True
           go AllChar        k s      = not (P.null s) && k (P.drop 1 s)
           go None           _ _      = False
           go (Range _ _)    _ []     = False
           go (Range a b)    k (c:cs) = a <= c && c <= b && k cs
           go (Conc [])      k s      = k s
           go (Conc (r:rs))  k s      = go r (go (Conc rs) k) s
           go (KStar r)      k s      = k s || go r (smaller (P.length s) (go (KStar r) k)) s
           go (KPlus r)      k s      = go (Conc [r, KStar r]) k s
           go (Opt r)        k s      = k s || go r k s
           go (Comp r)       k s      = not $ go r k s
           go (Diff r1 r2)   k s      = go r1 k s && not (go r2 k s)
           go (Loop i j r)   k s      = go (Conc (P.replicate i r P.++ P.replicate (j - i) (Opt r))) k s
           go (Power n r)    k s      = go (Loop n n r) k s
           go (Union [])     _ _      = False
           go (Union [x])    k s      = go x k s
           go (Union (x:xs)) k s      = go x k s || go (Union xs) k s
           go (Inter a b)    k s      = go a k s && go b k s

           -- In the KStar case, make sure the continuation is called with something
           -- smaller to avoid infinite recursion!
           smaller orig k inp = P.length inp < orig && k inp

-- | Match everything, universal acceptor.
--
-- >>> prove $ \(s :: SString) -> s `match` everything
-- Q.E.D.
everything :: RegExp
everything = All

-- | Match nothing, universal rejector.
--
-- >>> prove $ \(s :: SString) -> sNot (s `match` nothing)
-- Q.E.D.
nothing :: RegExp
nothing = None

-- | Match any character, i.e., strings of length 1
--
-- >>> prove $ \(s :: SString) -> s `match` anyChar .<=> length s .== 1
-- Q.E.D.
anyChar :: RegExp
anyChar = AllChar

-- | A literal regular-expression, matching the given string exactly. Note that
-- with @OverloadedStrings@ extension, you can simply use a Haskell
-- string to mean the same thing, so this function is rarely needed.
--
-- >>> prove $ \(s :: SString) -> s `match` exactly "LITERAL" .<=> s .== "LITERAL"
-- Q.E.D.
exactly :: String -> RegExp
exactly = Literal

-- | Helper to define a character class.
--
-- >>> prove $ \(c :: SChar) -> c `match` oneOf "ABCD" .<=> sAny (c .==) (P.map literal "ABCD")
-- Q.E.D.
oneOf :: String -> RegExp
oneOf xs = Union [exactly [x] | x <- xs]

-- | Recognize a newline. Also includes carriage-return and form-feed.
--
-- >>> newline
-- (re.union (str.to.re "\n") (str.to.re "\r") (str.to.re "\f"))
-- >>> prove $ \c -> c `match` newline .=> isSpaceL1 c
-- Q.E.D.
newline :: RegExp
newline = oneOf "\n\r\f"

-- | Recognize a tab.
--
-- >>> tab
-- (str.to.re "\t")
-- >>> prove $ \c -> c `match` tab .=> c .== literal '\t'
-- Q.E.D.
tab :: RegExp
tab = oneOf "\t"

-- | Lift a char function to a regular expression that recognizes it.
liftPredL1 :: (Char -> Bool) -> RegExp
liftPredL1 predicate = oneOf $ P.filter predicate (P.map C.chr [0 .. 255])

-- | Recognize white-space, but without a new line.
--
-- >>> prove $ \c -> c `match` whiteSpaceNoNewLine .=> c `match` whiteSpace .&& c ./= literal '\n'
-- Q.E.D.
whiteSpaceNoNewLine :: RegExp
whiteSpaceNoNewLine = liftPredL1 (\c -> C.isSpace c && c `P.notElem` ("\n" :: String))

-- | Recognize white space.
--
-- >>> prove $ \c -> c `match` whiteSpace .=> isSpaceL1 c
-- Q.E.D.
whiteSpace :: RegExp
whiteSpace = liftPredL1 C.isSpace

-- | Recognize a punctuation character.
--
-- >>> prove $ \c -> c `match` punctuation .=> isPunctuationL1 c
-- Q.E.D.
punctuation :: RegExp
punctuation = liftPredL1 C.isPunctuation

-- | Recognize an alphabet letter, i.e., @A@..@Z@, @a@..@z@.
asciiLetter :: RegExp
asciiLetter = asciiLower + asciiUpper

-- | Recognize an ASCII lower case letter
--
-- >>> asciiLower
-- (re.range "a" "z")
-- >>> prove $ \(c :: SChar) -> c `match` asciiLower  .=> c `match` asciiLetter
-- Q.E.D.
-- >>> prove $ \(c :: SChar) -> c `match` asciiLower  .=> toUpperL1 c `match` asciiUpper
-- Q.E.D.
-- >>> prove $ \(c :: SChar) -> c `match` asciiLetter .=> toLowerL1 c `match` asciiLower
-- Q.E.D.
asciiLower :: RegExp
asciiLower = Range 'a' 'z'

-- | Recognize an upper case letter
--
-- >>> asciiUpper
-- (re.range "A" "Z")
-- >>> prove $ \(c :: SChar) -> c `match` asciiUpper  .=> c `match` asciiLetter
-- Q.E.D.
-- >>> prove $ \(c :: SChar) -> c `match` asciiUpper  .=> toLowerL1 c `match` asciiLower
-- Q.E.D.
-- >>> prove $ \(c :: SChar) -> c `match` asciiLetter .=> toUpperL1 c `match` asciiUpper
-- Q.E.D.
asciiUpper :: RegExp
asciiUpper = Range 'A' 'Z'

-- | Recognize a digit. One of @0@..@9@.
--
-- >>> digit
-- (re.range "0" "9")
-- >>> prove $ \c -> c `match` digit .<=> let v = digitToInt c in 0 .<= v .&& v .< 10
-- Q.E.D.
-- >>> prove $ \c -> sNot ((c::SChar) `match` (digit - digit))
-- Q.E.D.
digit :: RegExp
digit = Range '0' '9'

-- | Recognize an octal digit. One of @0@..@7@.
--
-- >>> octDigit
-- (re.range "0" "7")
-- >>> prove $ \c -> c `match` octDigit .<=> let v = digitToInt c in 0 .<= v .&& v .< 8
-- Q.E.D.
-- >>> prove $ \(c :: SChar) -> c `match` octDigit .=> c `match` digit
-- Q.E.D.
octDigit :: RegExp
octDigit = Range '0' '7'

-- | Recognize a hexadecimal digit. One of @0@..@9@, @a@..@f@, @A@..@F@.
--
-- >>> hexDigit
-- (re.union (re.range "0" "9") (re.range "a" "f") (re.range "A" "F"))
-- >>> prove $ \c -> c `match` hexDigit .<=> let v = digitToInt c in 0 .<= v .&& v .< 16
-- Q.E.D.
-- >>> prove $ \(c :: SChar) -> c `match` digit .=> c `match` hexDigit
-- Q.E.D.
hexDigit :: RegExp
hexDigit = digit + Range 'a' 'f' + Range 'A' 'F'

-- | Recognize a decimal number.
--
-- >>> decimal
-- (re.+ (re.range "0" "9"))
-- >>> prove $ \(s :: SString) -> s `match` decimal .=> sNot (s `match` KStar asciiLetter)
-- Q.E.D.
decimal :: RegExp
decimal = KPlus digit

-- | Recognize an octal number. Must have a prefix of the form @0o@\/@0O@.
--
-- >>> octal
-- (re.++ (re.union (str.to.re "0o") (str.to.re "0O")) (re.+ (re.range "0" "7")))
-- >>> prove $ \(s :: SString) -> s `match` octal .=> sAny (.== take 2 s) ["0o", "0O"]
-- Q.E.D.
octal :: RegExp
octal = ("0o" + "0O") * KPlus octDigit

-- | Recognize a hexadecimal number. Must have a prefix of the form @0x@\/@0X@.
--
-- >>> hexadecimal
-- (re.++ (re.union (str.to.re "0x") (str.to.re "0X")) (re.+ (re.union (re.range "0" "9") (re.range "a" "f") (re.range "A" "F"))))
-- >>> prove $ \(s :: SString) -> s `match` hexadecimal .=> sAny (.== take 2 s) ["0x", "0X"]
-- Q.E.D.
hexadecimal :: RegExp
hexadecimal = ("0x" + "0X") * KPlus hexDigit

-- | Recognize a floating point number. The exponent part is optional if a fraction
-- is present. The exponent may or may not have a sign.
--
-- >>> prove $ \(s :: SString) -> s `match` floating .=> length s .>= 3
-- Q.E.D.
floating :: RegExp
floating = withFraction + withoutFraction
  where withFraction    = decimal * "." * decimal * Opt expt
        withoutFraction = decimal * expt
        expt            = ("e" + "E") * Opt (oneOf "+-") * decimal

-- | For the purposes of this regular expression, an identifier consists of a letter
-- followed by zero or more letters, digits, underscores, and single quotes. The first
-- letter must be lowercase.
--
-- >>> prove $ \(s :: SString) -> s `match` identifier .=> isAsciiLower (head s)
-- Q.E.D.
-- >>> prove $ \(s :: SString) -> s `match` identifier .=> length s .>= 1
-- Q.E.D.
identifier :: RegExp
identifier = asciiLower * KStar (asciiLetter + digit + "_" + "'")

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

-- | Concrete evaluation for unary ops
concEval1 :: (SymVal a, SymVal b) => Maybe (a -> b) -> SBV a -> Maybe (SBV b)
concEval1 mbOp a = literal <$> (mbOp <*> unliteral a)

-- | Quiet GHC about testing only imports
__unused :: a
__unused = undefined isSpaceL1

{- $matching
A symbolic string or a character ('SString' or 'SChar') can be matched against a regular-expression. Note
that the regular-expression itself is not a symbolic object: It's a fully concrete representation, as
captured by the 'RegExp' class. The 'RegExp' class is an instance of the @IsString@ class, which makes writing
literal matches easier. The 'RegExp' type also has a (somewhat degenerate) 'Num' instance: Concatenation
corresponds to multiplication, union corresponds to addition, and @0@ corresponds to the empty language.

Note that since `match` is a method of 'RegExpMatchable' class, both 'SChar' and 'SString' can be used as
an argument for matching. In practice, this means you might have to disambiguate with a type-ascription
if it is not deducible from context.

>>> prove $ \(s :: SString) -> s `match` "hello" .<=> s .== "hello"
Q.E.D.
>>> prove $ \(s :: SString) -> s `match` Loop 2 5 "xyz" .=> length s .>= 6
Q.E.D.
>>> prove $ \(s :: SString) -> s `match` Loop 2 5 "xyz" .=> length s .<= 15
Q.E.D.
>>> prove $ \(s :: SString) -> s `match` Power 3 "xyz" .=> length s .== 9
Q.E.D.
>>> prove $ \(s :: SString) -> s `match`  (exactly "xyz" ^ 3) .=> length s .== 9
Q.E.D.
>>> prove $ \(s :: SString) -> match s (Loop 2 5 "xyz") .=> length s .>= 7
Falsifiable. Counter-example:
  s0 = "xyzxyz" :: String
>>> prove $ \(s :: SString) -> s `match` "hello" .=> s `match` ("hello" + "world")
Q.E.D.
>>> prove $ \(s :: SString) -> sNot $ s `match` ("so close" * 0)
Q.E.D.
>>> prove $ \c -> (c :: SChar) `match` oneOf "abcd" .=> ord c .>= ord (literal 'a') .&& ord c .<= ord (literal 'd')
Q.E.D.
-}


{- $regexpeq
/A note on Equality/ Regular expressions can be symbolically compared for equality. Note that the regular Haskell 'Eq'
instance and the symbolic version differ in semantics: 'Eq' instance checks for "structural" equality, i.e., that the two regular expressions
are constructed in precisely the same way. The symbolic equality, however, checks for language equality, i.e., that
the regular expressions correspond to the same set of strings. This is a bit unfortunate, but hopefully should not
cause much trouble in practice. Note that the only reason we support symbolic equality is to take advantage of
the internal decision procedures z3 provides for this case: A similar goal can be achieved by showing there is
no string accepted by one but not the other. However, this encoding doesn't perform well in z3.

>>> prove $ ("a" * KStar ("b" * "a")) .== (KStar ("a" * "b") * "a")
Q.E.D.
>>> prove $ ("a" * KStar ("b" * "a")) .== (KStar ("a" * "b") * "c")
Falsifiable
>>> prove $ ("a" * KStar ("b" * "a")) ./= (KStar ("a" * "b") * "c")
Q.E.D.
-}
