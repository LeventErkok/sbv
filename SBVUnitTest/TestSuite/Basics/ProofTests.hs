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

module TestSuite.Basics.ProofTests(testSuite)  where

import Data.SBV

import Examples.Basics.ProofTests
import SBVTest

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "proofs-1"  ~: assert       =<< isThm f1eqf2
 , "proofs-2"  ~: assert . not =<< isThm f1eqf3
 , "proofs-3"  ~: assert       =<< isThm f3eqf4
 , "proofs-4"  ~: assert       =<< isThm f1Single
 , "proofs-5"  ~: assert       =<< isSat (f1 `xyEq` f2)
 , "proofs-6"  ~: assert       =<< isSat (f1 `xyEq` f3)
 , "proofs-7"  ~: assert . not =<< isSat (exists "x" >>= \x -> return (x .== x + (1 :: SWord16)))
 , "proofs-8"  ~: assert       =<< isSat (exists "x" >>= \x -> return (x :: SBool))
 , "proofs-9"  ~: assert       =<< isSat (exists "x" >>= \x -> return x :: Predicate)
 ]
 where func1 `xyEq` func2 = do x <- exists_
                               y <- exists_
                               return $ func1 x y .== func2 x (y :: SWord8)
