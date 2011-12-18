-----------------------------------------------------------------------------
-- |
-- Module      :  Examples.Basics.ProofTests
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Basic proofs
-----------------------------------------------------------------------------

{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Examples.Basics.ProofTests where

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
             print =<< sat (do x <- exists "x"
                               y <- exists "y"
                               return $ f1 x y .== f2 x (y :: SWord8))  -- yes, any output OK
             print =<< sat (do x <- exists "x"
                               y <- exists "y"
                               return $ f1 x y .== f3 x (y:: SWord8))    -- yes, 0;0
