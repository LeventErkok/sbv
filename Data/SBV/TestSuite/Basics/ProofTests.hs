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
 , "proofs-5"  ~: assert       =<< isSatisfiable f1eqf2
 , "proofs-6"  ~: assert       =<< isSatisfiable f1eqf3
 , "proofs-7"  ~: assert . not =<< isSatisfiable (\x -> x .== x + (1 :: SWord16))
 , "proofs-8"  ~: assert       =<< isSatisfiable (\x -> x :: SBool)
 , "proofs-9"  ~: assert       =<< isSatisfiable (\x -> return x :: Predicate)
 , "proofs-10" ~: assert       =<< isSatisfiable (forAll_ $ \x -> x :: SBool)
 , "proofs-11" ~: assert       =<< isSatisfiable (forAll_ $ \x -> return x :: Predicate)
 , "proofs-12" ~: assert       =<< isSatisfiable (forAll ["q"] $ \x -> x :: SBool)
 , "proofs-13" ~: assert       =<< isSatisfiable (forAll ["q"] $ \x -> return x :: Predicate)
 ]
