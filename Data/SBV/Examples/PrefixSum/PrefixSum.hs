{- (c) Copyright Levent Erkok. All rights reserved.
--
-- The sbv library is distributed with the BSD3 license. See the LICENSE file
-- in the distribution for details.
-}

{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- PrefixSum's over powerlists, proving equivalence of
-- the reference algorithm against Fischer-Ladner version

module Data.SBV.Examples.PrefixSum.PrefixSum where

import Data.SBV

-- A poor man's representation of powerlists and
-- basic operations on them:
type PowerList a = [a]

tiePL :: PowerList a -> PowerList a -> PowerList a
tiePL = (++)

zipPL :: PowerList a -> PowerList a -> PowerList a
zipPL []     []     = []
zipPL (x:xs) (y:ys) = x : y : zipPL xs ys
zipPL _      _      = error "zipPL: nonsimilar powerlists received"

unzipPL :: PowerList a -> (PowerList a, PowerList a)
unzipPL = unzip . chunk2
  where chunk2 []       = []
        chunk2 (x:y:xs) = (x,y) : chunk2 xs
        chunk2 _        = error "fl.unzipPL: malformed powerlist"

-- Reference prefix sum is simply scanl1
ps :: (a, a -> a -> a) -> PowerList a -> PowerList a
ps (_, f) = scanl1 f

-- Fischer-Ladner version
fl :: (a, a -> a -> a) -> PowerList a -> PowerList a
fl _ []         = error "fl: malformed (empty) powerlist"
fl _ [x]        = [x]
fl (zero, f) pl = zipPL (zipWith f (rsh flpq) p) flpq
   where (p, q) = unzipPL pl
         pq     = zipWith f p q
         flpq   = fl (zero, f) pq
         rsh xs = zero : init xs

-- Correctness theorem, for a powerlist of given size and
-- an associative operator. We'll run the symbolic execution over Word32's
flIsCorrect :: Int -> (forall a. (OrdSymbolic a, Bits a) => (a, a -> a -> a)) -> Symbolic SBool
flIsCorrect n zf = do
        args :: PowerList SWord32 <- mapM (const free_) [1..n]
        output $ ps zf args .== fl zf args

-- Instances that can be proven directly:
thm1, thm2 :: IO ThmResult
thm1 = prove $ flIsCorrect  8 (0, (+))
thm2 = prove $ flIsCorrect 16 (0, smax)

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "prefixSum1" ~: assert =<< isTheorem (flIsCorrect  8 (0, (+)))
 , "prefixSum1" ~: assert =<< isTheorem (flIsCorrect 16 (0, smax))
 ]
