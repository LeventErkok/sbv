-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Uninterpreted.Sort
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for uninterpreted sorts
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TestSuite.Uninterpreted.Sort(tests) where

import Utils.SBVTestFramework
import Data.Generics

tests :: TestTree
tests =
  testGroup "Uninterpreted.Sort"
    [ testCase "unint-sort"
        (assert . (==4) . length . (extractModels :: AllSatResult -> [L]) =<< allSat p0)
    ]

data L = Nil | Cons Int L deriving (Eq, Ord, Data, Read, Show)
instance SymWord L
instance HasKind L
instance SatModel L where
  parseCWs = undefined -- make GHC shut up about the missing method, we won't actually call it

type UList = SBV L

len :: UList -> SInteger
len = uninterpret "len"

p0 :: Symbolic SBool
p0 = do
    [l, l0, l1] <- symbolics ["l", "l0", "l1"]
    constrain $ len l0 .== 0
    constrain $ len l1 .== 1
    x :: SInteger <- symbolic "x"
    constrain $ x .== 0 ||| x.== 1
    return $ l .== l0 ||| l .== l1
