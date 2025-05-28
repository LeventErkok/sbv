-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.String
-- Copyright : (c) Joel Burget
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A collection of string/character utilities, useful when working
-- with symbolic strings. To the extent possible, the functions
-- in this module follow those of "Data.List" so importing qualified
-- is the recommended workflow. Also, it is recommended you use the
-- @OverloadedStrings@ extension to allow literal strings to be
-- used as symbolic-strings.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.String (
        -- * emptiness
           null
        -- * Deconstructing/Reconstructing
        , implode, nil
        -- * Conversion to\/from naturals
        , strToNat, natToStr
        ) where

import Prelude hiding (head, tail, init, length, take, drop, concat, null, reverse, (++), (!!))
import qualified Prelude as P

import Data.SBV.Core.Data hiding (SeqOp(..))

import qualified Data.Char as C

import Data.Proxy

import qualified Data.SBV.List as SL

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV
-- >>> import Prelude hiding (head, tail, init, length, take, drop, concat, null, reverse, (++), (!!))
-- >>> :set -XOverloadedStrings
#endif

-- | @`null` s@ is True iff the string is empty
--
-- >>> prove $ \s -> null s .<=> length s .== 0
-- Q.E.D.
-- >>> prove $ \s -> null s .<=> s .== ""
-- Q.E.D.
null :: SString -> SBool
null s
  | Just cs <- unliteral s
  = literal (P.null cs)
  | True
  = s .== literal ""

-- | @`implode` cs@ is the string of length @|cs|@ containing precisely those
-- characters. Note that there is no corresponding function @explode@, since
-- we wouldn't know the length of a symbolic string.
--
-- >>> prove $ \c1 c2 c3 -> length (implode [c1, c2, c3]) .== 3
-- Q.E.D.
-- >>> prove $ \c1 c2 c3 -> map (strToCharAt (implode [c1, c2, c3])) (map literal [0 .. 2]) .== [c1, c2, c3]
-- Q.E.D.
implode :: [SChar] -> SString
implode = foldr ((SL.++) . (SL.singleton)) ""

-- | Empty string. This value has the property that it's the only string with length 0:
--
-- >>> prove $ \l -> length l .== 0 .<=> l .== nil
-- Q.E.D.
nil :: SString
nil = ""

-- | @`strToNat` s@. Retrieve integer encoded by string @s@ (ground rewriting only).
-- Note that by definition this function only works when @s@ only contains digits,
-- that is, if it encodes a natural number. Otherwise, it returns '-1'.
--
-- >>> prove $ \s -> let n = strToNat s in length s .== 1 .=> (-1) .<= n .&& n .<= 9
-- Q.E.D.
strToNat :: SString -> SInteger
strToNat s
 | Just a <- unliteral s
 = if all C.isDigit a && not (P.null a)
   then literal (read a)
   else -1
 | True
 = lift1 StrStrToNat Nothing s

-- | @`natToStr` i@. Retrieve string encoded by integer @i@ (ground rewriting only).
-- Again, only naturals are supported, any input that is not a natural number
-- produces empty string, even though we take an integer as an argument.
--
-- >>> prove $ \i -> length (natToStr i) .== 3 .=> i .<= 999
-- Q.E.D.
natToStr :: SInteger -> SString
natToStr i
 | Just v <- unliteral i
 = literal $ if v >= 0 then show v else ""
 | True
 = lift1 StrNatToStr Nothing i

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

{- HLint ignore implode "Use concatMap" -}
