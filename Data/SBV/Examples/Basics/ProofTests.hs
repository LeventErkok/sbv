{- (c) Copyright Levent Erkok. All rights reserved.
--
-- The sbv library is distributed with the BSD3 license. See the LICENSE file
-- in the distribution for details.
-}

{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Examples.Basics.ProofTests where

import Data.SBV

f1, f2, f3, f4 :: Num a => a -> a -> a
f1 x y = (x+y)*(x-y)
f2 x y = (x*x)-(y*y)
f3 x y = (x+y)*(x+y)
f4 x y = x*x + 2*x*y + y*y

f1eqf2 :: Predicate
f1eqf2 = forAll_ $ \x y -> f1 x y .== f2 x (y :: SWord8)

f1eqf3 :: Predicate
f1eqf3 = forAll ["x", "y"] $ \x y -> f1 x y .== f3 x (y :: SWord8)

f3eqf4 :: Predicate
f3eqf4 = forAll_ $ \x y -> f3 x y .== f4 x (y :: SWord8)

f1Single :: Predicate
f1Single = forAll_ $ \x -> f1 x x .== (0 :: SWord16)

queries :: IO ()
queries = do print =<< prove f1eqf2   -- QED
             print =<< prove f1eqf3   -- No
             print =<< prove f3eqf4   -- QED
             print =<< prove f1Single -- QED
             print =<< sat f1eqf2     -- yes. any output ok
             print =<< sat f1eqf3     -- yes, 0;0

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "proofs-1"  ~: assert       =<< isTheorem f1eqf2
 , "proofs-2"  ~: assert . not =<< isTheorem f1eqf3
 , "proofs-3"  ~: assert       =<< isTheorem f3eqf4
 , "proofs-4"  ~: assert       =<< isTheorem f1Single
 , "proofs-5"  ~: assert       =<< isSatisfiable f1eqf2
 , "proofs-6"  ~: assert       =<< isSatisfiable f1eqf3
 , "proofs-7"  ~: assert . not =<< isSatisfiable (\x -> x .== x+(1 :: SWord16))
 ]
