-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.ProofTests
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Examples.Basics.ProofTests
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.ProofTests(tests)  where

import Utils.SBVTestFramework

tests :: TestTree
tests =
  testGroup "Basics.Proof"
    [ testCase "proofs-1" (assertIsThm   f1eqf2)
    , testCase "proofs-2" (assertIsntThm f1eqf3)
    , testCase "proofs-3" (assertIsThm   f3eqf4)
    , testCase "proofs-4" (assertIsThm   f1Single)
    , testCase "proofs-5" (assertIsSat   (f1 `xyEq` f2))
    , testCase "proofs-6" (assertIsSat   (f1 `xyEq` f3))
    , testCase "proofs-7" (assertIsntSat (free "x" >>= \x -> return (x .== x + (1 :: SWord16))))
    , testCase "proofs-8" (assertIsSat   (free "x" >>= \x -> return (x :: SBool)))
    , testCase "proofs-9" (assertIsSat   (free "x" >>= \x -> return x :: Predicate))
    ]

xyEq :: (EqSymbolic a, SymVal a1) => (SBV a1 -> SBV Word8 -> a) -> (SBV a1 -> SWord8 -> a) -> Symbolic SBool
func1 `xyEq` func2 = do x <- free_
                        y <- free_
                        return $ func1 x y .== func2 x (y :: SWord8)

f1, f2, f3, f4 :: Num a => a -> a -> a
f1 x y = (x+y)*(x-y)
f2 x y = (x*x)-(y*y)
f3 x y = (x+y)*(x+y)
f4 x y = x*x + 2*x*y + y*y

f1eqf2 :: Predicate
f1eqf2 = pure $ quantifiedBool $ \(Forall x) (Forall y) -> f1 x y .== f2 x (y :: SWord8)

f1eqf3 :: Predicate
f1eqf3 = pure $ quantifiedBool $ \(Forall x) (Forall y) -> f1 x y .== f3 x (y :: SWord8)

f3eqf4 :: Predicate
f3eqf4 = pure $ quantifiedBool $ \(Forall x) (Forall y) -> f3 x y .== f4 x (y :: SWord8)

f1Single :: Predicate
f1Single = pure $ quantifiedBool $ \(Forall x) -> f1 x x .== (0 :: SWord16)
