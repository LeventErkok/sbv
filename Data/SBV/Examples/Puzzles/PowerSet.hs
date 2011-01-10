-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Puzzles.PowerSet
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Computes the powerset of a givenset
-----------------------------------------------------------------------------

module Data.SBV.Examples.Puzzles.PowerSet where

import Data.SBV
import Data.SBV.Utils.SBVTest

-- the seemingly vacuous test ".<= true" is necessary
-- so that Yices will return a satisfying assignment
-- otherwise, it just skips the "unused" inputs..
genPowerSet :: [SBool] -> SBool
-- genPowerSet = const true   -- this is what I'd like to write.. see above
genPowerSet = bAll (.<= (true :: SBool))

powerSet :: [Word8] -> IO ()
powerSet xs = do putStrLn $ "Finding all subsets of " ++ show xs
                 res <- allSat $ mapM (const free_) [1..n] >>= output . genPowerSet
                 cnt <- displayModels disp res
                 putStrLn $ "Found: " ++ show cnt ++ " subset(s)."
     where n = length xs
           disp i ss
            | length ss /= n = error $ "Expected " ++ show n ++ " results; got: " ++ show (length ss)
            | True           = putStrLn $ "Subset #" ++ show i ++ ": " ++ show (concat (zipWith pick ss xs))
           pick True a  = [a]
           pick False _ = []

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [ "powerSet " ++ show i ~: assert (pSet i) | i <- [0 .. 7] ]
 where pSet :: Int -> IO Bool
       pSet n = do cnt <- numberOfModels $ mapM (const free_) [1 .. n] >>= output . genPowerSet
                   return (cnt == 2^n)
