{- (c) Copyright Levent Erkok. All rights reserved.
--
-- The sbv library is distributed with the BSD3 license. See the LICENSE file
-- in the distribution for details.
-}

module Data.SBV.Examples.Puzzles.NQueens where

import Data.SBV

type Solution = [SWord8]

isValid :: Int -> Solution -> SBool
isValid n s = bAll rangeFine s &&& allDifferent s &&& bAll checkDiag ijs
  where rangeFine x = x .>= 1 &&& x .<= fromIntegral n
        ijs = [(i, j) | i <- [1..n], j <- [i+1..n]]
        checkDiag (i, j) = diffR ./= diffC
           where qi = s !! (i-1)
                 qj = s !! (j-1)
                 diffR = ite (qi .>= qj) (qi-qj) (qj-qi)
                 diffC = fromIntegral (j-i)

nQueens :: Int -> IO ()
nQueens n
 | n < 0 = putStrLn $ "n must be non-negative, received: " ++ show n
 | True  = do putStrLn $ "Finding all " ++ show n ++ "-queens solutions.."
              res <- allSat $ mapM (const free_) [1..n] >>= output . isValid n
              cnt <- displayModels disp res
              putStrLn $ "Found: " ++ show cnt ++ " solution(s)."
   where disp i s = do putStr $ "Solution #" ++ show i ++ ": "
                       dispSolution n s

dispSolution :: Int -> [Word8] -> IO ()
dispSolution n model
  | lmod /= n = error $ "Impossible! Backend solver returned " ++ show lmod ++ " values, was expecting: " ++ show n
  | True      = do putStr $ show model
                   putStrLn $ " (Valid: " ++ show (isValid n (map literal model)) ++ ")"
    where lmod  = length model

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   -- number of *distinct* solutions is given in http://en.wikipedia.org/wiki/Eight_queens_puzzle
   "nQueens 1" ~: assert $ (==  1) `fmap` numberOfModels (mkQueens 1)
 , "nQueens 2" ~: assert $ (==  0) `fmap` numberOfModels (mkQueens 2)
 , "nQueens 3" ~: assert $ (==  0) `fmap` numberOfModels (mkQueens 3)
 , "nQueens 4" ~: assert $ (==  2) `fmap` numberOfModels (mkQueens 4)
 , "nQueens 5" ~: assert $ (== 10) `fmap` numberOfModels (mkQueens 5)
 , "nQueens 6" ~: assert $ (==  4) `fmap` numberOfModels (mkQueens 6)
 , "nQueens 7" ~: assert $ (== 40) `fmap` numberOfModels (mkQueens 7)
 , "nQueens 8" ~: assert $ (== 92) `fmap` numberOfModels (mkQueens 8)
 ]
 where mkQueens n = mapM (const free_) [1 .. n] >>= output . isValid n
