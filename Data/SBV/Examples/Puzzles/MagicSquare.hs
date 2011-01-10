-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Puzzles.MagicSquare
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Solves the magic-square puzzle
-----------------------------------------------------------------------------

module Data.SBV.Examples.Puzzles.MagicSquare where

import Data.List
import Data.SBV
import Data.SBV.Utils.SBVTest

type Elem  = SWord32
type Row   = [Elem]
type Board = [Row]

check :: Elem -> Elem -> Row -> SBool
check low high grp = bAll rangeFine grp
  where rangeFine x = x .>= low &&& x .<= high

diag :: [[a]] -> [a]
diag ((a:_):rs) = a : diag (map tail rs)
diag _          = []

isMagic :: Board -> SBool
isMagic rows = bAnd $ fromBool isSquare : allEqual (map sum items) : allDifferent (concat rows) : map chk items
  where items = d1 : d2 : rows ++ columns
        n = genericLength rows
        isSquare = all (\r -> genericLength r == n) rows
        columns = transpose rows
        d1 = diag rows
        d2 = diag (map reverse rows)
        chk = check (literal 1) (literal (n*n))

chunk :: Int -> [a] -> [[a]]
chunk _ [] = []
chunk i xs = let (f, r) = splitAt i xs in f : chunk i r

magic :: Int -> IO ()
magic n
 | n < 0 = putStrLn $ "n must be non-negative, received: " ++ show n
 | True  = do putStrLn $ "Finding all " ++ show n ++ "-magic squares.."
              res <- allSat $ mapM (const free_) [1..n2] >>= output . isMagic . chunk n
              cnt <- displayModels disp res
              putStrLn $ "Found: " ++ show cnt ++ " solution(s)."
   where n2 = n * n
         disp i model
          | lmod /= n2
          = error $ "Impossible! Backend solver returned " ++ show n ++ " values, was expecting: " ++ show lmod
          | True
          = do putStrLn $ "Solution #" ++ show i
               mapM_ printRow board
               putStrLn $ "Valid Check: " ++ show (isMagic sboard)
               putStrLn "Done."
          where lmod  = length model
                board = chunk n $ model
                sboard = map (map literal) board
                sh2 z = let s = show z in if length s < 2 then ' ':s else s
                printRow r = putStr "   " >> mapM_ (\x -> putStr ((sh2 x) ++ " ")) r >> putStrLn ""

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "magic 2" ~: assert . not =<< isSatisfiable (mkMagic 2)
 , "magic 3" ~: assert       =<< isSatisfiable (mkMagic 3)
 ]
 where mkMagic n = mapM (const free_) [1 .. n*n] >>= output . isMagic . chunk n
