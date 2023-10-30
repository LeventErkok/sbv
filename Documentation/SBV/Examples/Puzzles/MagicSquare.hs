-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.MagicSquare
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Solves the magic-square puzzle. An NxN magic square is one where all entries
-- are filled with numbers from 1 to NxN such that sums of all rows, columns
-- and diagonals is the same.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Puzzles.MagicSquare where

import Data.List (genericLength, transpose)

import Data.SBV

-- | Use 32-bit words for elements.
type Elem  = SWord32

-- | A row is a list of elements
type Row   = [Elem]

-- | The puzzle board is a list of rows
type Board = [Row]

-- | Checks that all elements in a list are within bounds
check :: Elem -> Elem -> [Elem] -> SBool
check low high = sAll $ \x -> x .>= low .&& x .<= high

-- | Get the diagonal of a square matrix
diag :: [[a]] -> [a]
diag ((a:_):rs) = a : diag (map (drop 1) rs)
diag _          = []

-- | Test if a given board is a magic square
isMagic :: Board -> SBool
isMagic rows = sAnd $ fromBool isSquare : allEqual (map sum items) : distinct (concat rows) : map chk items
  where items = d1 : d2 : rows ++ columns
        n = genericLength rows
        isSquare = all (\r -> genericLength r == n) rows
        columns = transpose rows
        d1 = diag rows
        d2 = diag (map reverse rows)
        chk = check (literal 1) (literal (n*n))

-- | Group a list of elements in the sublists of length @i@
chunk :: Int -> [a] -> [[a]]
chunk _ [] = []
chunk i xs = let (f, r) = splitAt i xs in f : chunk i r

-- | Given @n@, magic @n@ prints all solutions to the @nxn@ magic square problem
magic :: Int -> IO ()
magic n
 | n < 0 = putStrLn $ "n must be non-negative, received: " ++ show n
 | True  = do putStrLn $ "Finding all " ++ show n ++ "-magic squares.."
              res <- allSat $ (isMagic . chunk n) `fmap` mkFreeVars n2
              cnt <- displayModels id disp res
              putStrLn $ "Found: " ++ show cnt ++ " solution(s)."
   where n2 = n * n
         disp i (_, model)
          | lmod /= n2
          = error $ "Impossible! Backend solver returned " ++ show n ++ " values, was expecting: " ++ show lmod
          | True
          = do putStrLn $ "Solution #" ++ show i
               mapM_ printRow board
               putStrLn $ "Valid Check: " ++ show (isMagic sboard)
               putStrLn "Done."
          where lmod  = length model
                board = chunk n model
                sboard = map (map literal) board
                sh2 z = let s = show z in if length s < 2 then ' ':s else s
                printRow r = putStr "   " >> mapM_ (\x -> putStr (sh2 x ++ " ")) r >> putStrLn ""
