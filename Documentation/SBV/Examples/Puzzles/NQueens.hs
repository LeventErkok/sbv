-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.NQueens
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Solves the NQueens puzzle: <http://en.wikipedia.org/wiki/Eight_queens_puzzle>
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Puzzles.NQueens where

import Data.SBV

-- | A solution is a sequence of row-numbers where queens should be placed
type Solution = [SWord8]

-- | Checks that a given solution of @n@-queens is valid, i.e., no queen
-- captures any other.
isValid :: Int -> Solution -> SBool
isValid n s = sAll rangeFine s .&& distinct s .&& sAll checkDiag ijs
  where rangeFine x = x .>= 1 .&& x .<= fromIntegral n
        ijs = [(i, j) | i <- [1..n], j <- [i+1..n]]
        checkDiag (i, j) = diffR ./= diffC
           where qi = s !! (i-1)
                 qj = s !! (j-1)
                 diffR = ite (qi .>= qj) (qi-qj) (qj-qi)
                 diffC = fromIntegral (j-i)

-- | Given @n@, it solves the @n-queens@ puzzle, printing all possible solutions.
nQueens :: Int -> IO ()
nQueens n
 | n < 0 = putStrLn $ "n must be non-negative, received: " ++ show n
 | True  = do putStrLn $ "Finding all " ++ show n ++ "-queens solutions.."
              res <- allSat $ isValid n `fmap` mkFreeVars n
              cnt <- displayModels id disp res
              putStrLn $ "Found: " ++ show cnt ++ " solution(s)."
   where disp i (_, s) = do putStr $ "Solution #" ++ show i ++ ": "
                            dispSolution s
         dispSolution :: [Word8] -> IO ()
         dispSolution model
           | lmod /= n = error $ "Impossible! Backend solver returned " ++ show lmod ++ " values, was expecting: " ++ show n
           | True      = do putStr $ show model
                            putStrLn $ " (Valid: " ++ show (isValid n (map literal model)) ++ ")"
           where lmod  = length model
