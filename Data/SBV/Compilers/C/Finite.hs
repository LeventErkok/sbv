-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.Finite
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Finite SMT-object domains shared by C collection lowering.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.Finite (finiteDomainSize) where

import qualified Data.Set as Set

import Data.SBV.Core.Data

-- | Count distinct SMT objects without imposing a machine-integer limit.
-- All NaN encodings denote one object; signed zeros remain distinct. The
-- constructor callback resolves ADT references without a module dependency
-- cycle. Recursive and unbounded domains return 'Nothing'.
finiteDomainSize :: (Kind -> [[Kind]]) -> Kind -> Maybe Integer
finiteDomainSize constructorsOf = count Set.empty
 where count _ KBool                 = Just 2
       count _ (KBounded _ width)     = Just (2 ^ width)
       count _ KFloat                = Just (2 ^ (32 :: Int) - 2 ^ (24 :: Int) + 3)
       count _ KDouble               = Just (2 ^ (64 :: Int) - 2 ^ (53 :: Int) + 3)
       count _ KChar                 = Just 0x30000
       count _ (KFP eb sb)            = Just (2 ^ (eb + sb) - 2 ^ sb + 3)
       count seen (KTuple fields)     = product <$> mapM (count seen) fields
       count seen kind
         | isRoundingMode kind = Just 5
         | concrete kind, kind `Set.notMember` seen
         = sum <$> mapM (fmap product . mapM (count (Set.insert kind seen))) (constructorsOf kind)
         | True = Nothing

       concrete KApp{} = True
       concrete kind   = isADT kind && not (isUninterpreted kind)
