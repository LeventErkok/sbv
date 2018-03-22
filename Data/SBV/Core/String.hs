{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Core.String
-- Copyright   :  (c) Levent Erkok
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

-- TODO(joel): fill in concrete implementations

strConcat :: SString -> SString -> SString
strConcat = lift2 StrConcat (Just (++))

-- TODO(joel): add Monoid / Semigroup instances
infixr 5 .++
(.++) :: SString -> SString -> SString
(.++) = strConcat

strLen :: SString -> SInteger
strLen = lift1 StrLen (Just (fromIntegral . length))

strSubstr :: SString -> SInteger -> SInteger -> SString
strSubstr = lift3 StrSubstr Nothing

strIndexOf :: SString -> SString -> SInteger
strIndexOf = lift2 StrIndexOf Nothing

strOffsetIndexOf :: SString -> SString -> SInteger -> SInteger
strOffsetIndexOf = lift3 StrOffsetIndexOf Nothing

strAt :: SString -> SInteger -> SString
strAt = lift2 StrAt Nothing

strContains :: SString -> SString -> SBool
strContains = lift2 StrContains Nothing

strPrefixOf :: SString -> SString -> SBool
strPrefixOf = lift2 StrPrefixOf Nothing

strSuffixOf :: SString -> SString -> SBool
strSuffixOf = lift2 StrSuffixOf Nothing

strReplace :: SString -> SString -> SString -> SString
strReplace = lift3 StrReplace Nothing

strToInt :: SString -> SInteger
strToInt = lift1 StrToInt Nothing

intToStr :: SInteger -> SString
intToStr = lift1 IntToStr Nothing

lift1 :: forall a b. (SymWord a, SymWord b) => StrOp -> Maybe (a -> b) -> SBV a -> SBV b
lift1 w mbOp a
  | Just cv <- concEval1 mbOp a
  = cv
  | True
  = SBV $ SVal k $ Right $ cache r
  where k = kindOf (undefined :: b)
        r st = do swa <- sbvToSW st a
                  newExpr st k (SBVApp (StrOp w) [swa])

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

concEval1 :: (SymWord a, SymWord b) => Maybe (a -> b) -> SBV a -> Maybe (SBV b)
concEval1 mbOp a = literal <$> (mbOp <*> unliteral a)

concEval2 :: (SymWord a, SymWord b, SymWord c) => Maybe (a -> b -> c) -> SBV a -> SBV b -> Maybe (SBV c)
concEval2 mbOp a b = literal <$> (mbOp <*> unliteral a <*> unliteral b)

concEval3 :: (SymWord a, SymWord b, SymWord c, SymWord d) => Maybe (a -> b -> c -> d) -> SBV a -> SBV b -> SBV c -> Maybe (SBV d)
concEval3 mbOp a b c = literal <$> (mbOp <*> unliteral a <*> unliteral b <*> unliteral c)
