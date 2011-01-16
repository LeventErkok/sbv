-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Puzzles.NQueens
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Solves the NQueens puzzle
-----------------------------------------------------------------------------

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
