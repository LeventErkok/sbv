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

-- | `strSubStr s offset length` is the substring of `s` at offset `offset` with length `length`. When
-- the offset/length is out-of-bounds, the result is unspecified.
strSubstr :: SString -> SInteger -> SInteger -> SString
strSubstr = lift3 StrSubstr Nothing

-- | `strIndexOf s sub`. Retrieves first position of @sub@ in @s@, @-1@ if there are no occurrences.
strIndexOf :: SString -> SString -> SInteger
strIndexOf = lift2 StrIndexOf Nothing

-- | `strOffsetIndexOf s sub offset`. Retrieves first position of @sub@ at or after @offset@ in @s@, @-1@ if there are no occurrences.
strOffsetIndexOf :: SString -> SString -> SInteger -> SInteger
strOffsetIndexOf = lift3 StrOffsetIndexOf Nothing

-- | `strAt s offset`. Substring of length 1 at @offset@ in @s@.
strAt :: SString -> SInteger -> SString
strAt = lift2 StrAt Nothing

-- | `strContains s sub`. Does @s@ contain the substring @sub@?
strContains :: SString -> SString -> SBool
strContains = lift2 StrContains Nothing

-- | `strPrefixOf pre s`. Is @pre@ a prefix of @s@?
strPrefixOf :: SString -> SString -> SBool
strPrefixOf = lift2 StrPrefixOf Nothing

-- | `strSuffixOf suf s`. Is @suf@ a suffix of @s@?
strSuffixOf :: SString -> SString -> SBool
strSuffixOf = lift2 StrSuffixOf Nothing

-- | `strReplace s src dst`. Replace the first occurrence of @src@ by @dst@ in @s@
strReplace :: SString -> SString -> SString -> SString
strReplace = lift3 StrReplace Nothing

-- | `strToInt s`. Retrieve integer encoded by string @s@ (ground rewriting only)
strToInt :: SString -> SInteger
strToInt = lift1 StrToInt Nothing

-- | `intToStr i`. Retrieve string encoded by integer @i@ (ground rewriting only)
intToStr :: SInteger -> SString
intToStr = lift1 IntToStr Nothing

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
