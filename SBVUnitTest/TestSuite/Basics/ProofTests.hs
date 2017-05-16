-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Basics.ProofTests
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Examples.Basics.ProofTests
-----------------------------------------------------------------------------

module TestSuite.Basics.ProofTests(tests)  where

import Data.SBV

import Examples.Basics.ProofTests
import SBVTest

tests :: TestTree
tests =
  testGroup "Basics.Proof"
    [ testCase "proofs-1" (assertIsThm f1eqf2)
    , testCase "proofs-2" (assertIsntThm f1eqf3)
    , testCase "proofs-3" (assertIsThm f3eqf4)
    , testCase "proofs-4" (assertIsThm f1Single)
    , testCase "proofs-5" (assertIsSat (f1 `xyEq` f2))
    , testCase "proofs-6" (assertIsSat (f1 `xyEq` f3))
    , testCase "proofs-7" (assertIsntSat (exists "x" >>= \x -> return (x .== x + (1 :: SWord16))))
    , testCase "proofs-8" (assertIsSat (exists "x" >>= \x -> return (x :: SBool)))
    , testCase "proofs-9" (assertIsSat (exists "x" >>= \x -> return x :: Predicate))
    ]

xyEq ::
  (EqSymbolic a, SymWord a1) =>
    (SBV a1 -> SBV Word8 -> a) -> (SBV a1 -> SWord8 -> a) -> Symbolic SBool
func1 `xyEq` func2 = do x <- exists_
                        y <- exists_
                        return $ func1 x y .== func2 x (y :: SWord8)
