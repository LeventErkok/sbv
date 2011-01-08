{- (c) Copyright Levent Erkok. All rights reserved.
--
-- The sbv library is distributed with the BSD3 license. See the LICENSE file
-- in the distribution for details.
-}

module Data.SBV.Examples.Puzzles.PowerSet where

import Data.SBV

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
testSuite = mkTestSuite $ \_ -> test [
   "powerSet 0" ~: assert $ (== 2^0) `fmap` numberOfModels (mkPSet 0)
 , "powerSet 1" ~: assert $ (== 2^1) `fmap` numberOfModels (mkPSet 1)
 , "powerSet 2" ~: assert $ (== 2^2) `fmap` numberOfModels (mkPSet 2)
 , "powerSet 3" ~: assert $ (== 2^3) `fmap` numberOfModels (mkPSet 3)
 , "powerSet 4" ~: assert $ (== 2^4) `fmap` numberOfModels (mkPSet 4)
 , "powerSet 5" ~: assert $ (== 2^5) `fmap` numberOfModels (mkPSet 5)
 , "powerSet 6" ~: assert $ (== 2^6) `fmap` numberOfModels (mkPSet 6)
 , "powerSet 7" ~: assert $ (== 2^7) `fmap` numberOfModels (mkPSet 7)
 , "powerSet 8" ~: assert $ (== 2^8) `fmap` numberOfModels (mkPSet 8)
 ]
 where mkPSet n = mapM (const free_) [1 .. n] >>= output . genPowerSet
