-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.TestSuite.Basics.ProofTests
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test suite for Data.SBV.Examples.Basics.ProofTests
-----------------------------------------------------------------------------

module Data.SBV.TestSuite.Basics.ProofTests(testSuite)  where

import Data.SBV
import Data.SBV.Internals
import Data.SBV.Examples.Basics.ProofTests

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "proofs-1"  ~: assert       =<< isTheorem f1eqf2
 , "proofs-2"  ~: assert . not =<< isTheorem f1eqf3
 , "proofs-3"  ~: assert       =<< isTheorem f3eqf4
 , "proofs-4"  ~: assert       =<< isTheorem f1Single
 , "proofs-5"  ~: assert       =<< isSatisfiable (f1 `xyEq` f2)
 , "proofs-6"  ~: assert       =<< isSatisfiable (f1 `xyEq` f3)
 , "proofs-7"  ~: assert . not =<< isSatisfiable (exists "x" >>= \x -> return (x .== x + (1 :: SWord16)))
 , "proofs-8"  ~: assert       =<< isSatisfiable (exists "x" >>= \x -> return (x :: SBool))
 , "proofs-9"  ~: assert       =<< isSatisfiable (exists "x" >>= \x -> return x :: Predicate)
 ]
 where func1 `xyEq` func2 = do x <- exists_
                               y <- exists_
                               return $ func1 x y .== func2 x (y :: SWord8)
