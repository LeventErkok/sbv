-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.Sudoku
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- The Sudoku solver, quintessential SMT solver example!
-----------------------------------------------------------------------------

{-# LANGUAGE CPP              #-}
{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Puzzles.Sudoku where

#if MIN_VERSION_base(4,18,0)
import Control.Monad (when, zipWithM_)
#endif

import Control.Monad.State.Lazy

import Data.List     (transpose)

import Data.SBV
import Data.SBV.Control

-------------------------------------------------------------------
-- * Modeling Sudoku
-------------------------------------------------------------------
-- | A row is a sequence of digits that we represent symbolic integers
type Row = [SInteger]

-- | A Sudoku board is a sequence of 9 rows
type Board = [Row]

-- | Given a series of elements, make sure they are all different
-- and they all are numbers between 1 and 9
check :: [SInteger] -> SBool
check grp = sAnd $ distinct grp : map rangeFine grp
  where rangeFine x = x `inRange` (1, 9)

-- | Given a full Sudoku board, check that it is valid
valid :: Board -> SBool
valid rows = sAnd $ literal sizesOK : map check (rows ++ columns ++ squares)
  where sizesOK = length rows == 9 && all (\r -> length r == 9) rows

        columns = transpose rows
        regions = transpose [chunk 3 row | row <- rows]
        squares = [concat sq | sq <- chunk 3 (concat regions)]

        chunk :: Int -> [a] -> [[a]]
        chunk _ [] = []
        chunk i xs = let (f, r) = splitAt i xs in f : chunk i r

-- | A puzzle is simply a list of rows. Put 0 to indicate blanks.
type Puzzle = [[Integer]]

-------------------------------------------------------------------
-- * Solving Sudoku puzzles
-------------------------------------------------------------------

-- | Fill a given board, replacing 0's with appropriate elements to solve the puzzle
fillBoard :: Puzzle -> IO Puzzle
fillBoard board = runSMT $ do
     let emptyCellCount = length $ filter (== 0) $ concat board
     subst <- mkFreeVars emptyCellCount
     constrain $ valid (fill literal subst)

     query $ do cs <- checkSat
                case cs of
                  Sat   -> do vals <- mapM getValue subst
                              pure $ fill id vals
                  Unsat -> error "Unsolvable puzzle!"
                  _     -> error $ "Solver said: " ++ show cs

 where fill xform = evalState (mapM (mapM replace) board)
         where replace 0 = do supply <- get
                              case supply of
                                []     -> error "Run out of supplies while filling in the board!"
                                (s:ss) -> put ss >> pure s
               replace n = pure $ xform n

-- | Solve a given puzzle and print the results
sudoku :: Puzzle -> IO ()
sudoku board = fillBoard board >>= displayBoard
 where displayBoard :: Puzzle -> IO ()
       displayBoard puzzle = do
            let sh       i r = show r ++ if i `elem` [3, 6] then " " else ""
                printRow i r = do putStrLn $ "    " ++ unwords (zipWith sh [(1::Int)..] r)
                                  when (i `elem` [3, 6]) $ putStrLn ""
            zipWithM_ printRow [(1::Int)..] puzzle

            let isValid = valid (map (map literal) puzzle)
            case unliteral isValid of
               Just True  -> pure ()
               Just False -> error "Invalid solution generated!"
               Nothing    -> error "Impossible happened, got a symbolic result for valid."

-------------------------------------------------------------------
-- * Example boards
-------------------------------------------------------------------

-- | A random puzzle, found on the internet..
puzzle1 :: Puzzle
puzzle1 = [ [0, 6, 0,   0, 0, 0,   0, 1, 0]
          , [0, 0, 0,   6, 5, 1,   0, 0, 0]
          , [1, 0, 7,   0, 0, 0,   6, 0, 2]

          , [6, 2, 0,   3, 0, 5,   0, 9, 4]
          , [0, 0, 3,   0, 0, 0,   2, 0, 0]
          , [4, 8, 0,   9, 0, 7,   0, 3, 6]

          , [9, 0, 6,   0, 0, 0,   4, 0, 8]
          , [0, 0, 0,   7, 9, 4,   0, 0, 0]
          , [0, 5, 0,   0, 0, 0,   0, 7, 0] ]

-- | Another random puzzle, found on the internet..
puzzle2 :: Puzzle
puzzle2 = [ [1, 0, 3,   0, 0, 0,   0, 8, 0]
          , [0, 0, 6,   0, 4, 8,   0, 0, 0]
          , [0, 4, 0,   0, 0, 0,   0, 0, 0]

          , [2, 0, 0,   0, 9, 6,   1, 0, 0]
          , [0, 9, 0,   8, 0, 1,   0, 4, 0]
          , [0, 0, 4,   3, 2, 0,   0, 0, 8]

          , [0, 0, 0,   0, 0, 0,   0, 7, 0]
          , [0, 0, 0,   1, 5, 0,   4, 0, 0]
          , [0, 6, 0,   0, 0, 0,   2, 0, 3] ]

-- | Another random puzzle, found on the internet..
puzzle3 :: Puzzle
puzzle3 = [ [6, 0, 0,   0, 1, 0,   5, 0, 0]
          , [8, 0, 3,   0, 0, 0,   0, 0, 0]
          , [0, 0, 0,   0, 6, 0,   0, 2, 0]

          , [0, 3, 0,   1, 0, 8,   0, 9, 0]
          , [1, 0, 0,   0, 9, 0,   0, 0, 4]
          , [0, 5, 0,   2, 0, 3,   0, 1, 0]

          , [0, 7, 0,   0, 3, 0,   0, 0, 0]
          , [0, 0, 0,   0, 0, 0,   3, 0, 6]
          , [0, 0, 4,   0, 5, 0,   0, 0, 9] ]

-- | According to the web, this is the toughest 
-- sudoku puzzle ever.. It even has a name: Al Escargot:
-- <http://zonkedyak.blogspot.com/2006/11/worlds-hardest-sudoku-puzzle-al.html>
puzzle4 :: Puzzle
puzzle4 = [ [1, 0, 0,   0, 0, 7,   0, 9, 0]
          , [0, 3, 0,   0, 2, 0,   0, 0, 8]
          , [0, 0, 9,   6, 0, 0,   5, 0, 0]

          , [0, 0, 5,   3, 0, 0,   9, 0, 0]
          , [0, 1, 0,   0, 8, 0,   0, 0, 2]
          , [6, 0, 0,   0, 0, 4,   0, 0, 0]

          , [3, 0, 0,   0, 0, 0,   0, 1, 0]
          , [0, 4, 0,   0, 0, 0,   0, 0, 7]
          , [0, 0, 7,   0, 0, 0,   3, 0, 0] ]

-- | This one has been called diabolical, apparently
puzzle5 :: Puzzle
puzzle5 = [ [ 0, 9, 0,   7, 0, 0,   8, 6, 0]
          , [ 0, 3, 1,   0, 0, 5,   0, 2, 0]
          , [ 8, 0, 6,   0, 0, 0,   0, 0, 0]

          , [ 0, 0, 7,   0, 5, 0,   0, 0, 6]
          , [ 0, 0, 0,   3, 0, 7,   0, 0, 0]
          , [ 5, 0, 0,   0, 1, 0,   7, 0, 0]

          , [ 0, 0, 0,   0, 0, 0,   1, 0, 9]
          , [ 0, 2, 0,   6, 0, 0,   3, 5, 0]
          , [ 0, 5, 4,   0, 0, 8,   0, 7, 0] ]

-- | The following is nefarious according to
-- <http://haskell.org/haskellwiki/Sudoku>
puzzle6 :: Puzzle
puzzle6 = [ [0, 0, 0,   0, 6, 0,   0, 8, 0]
          , [0, 2, 0,   0, 0, 0,   0, 0, 0]
          , [0, 0, 1,   0, 0, 0,   0, 0, 0]

          , [0, 7, 0,   0, 0, 0,   1, 0, 2]
          , [5, 0, 0,   0, 3, 0,   0, 0, 0]
          , [0, 0, 0,   0, 0, 0,   4, 0, 0]

          , [0, 0, 4,   2, 0, 1,   0, 0, 0]
          , [3, 0, 0,   7, 0, 0,   6, 0, 0]
          , [0, 0, 0,   0, 0, 0,   0, 5, 0] ]

-- | Solve them all, this takes a fraction of a second to run for each case
allPuzzles :: IO ()
allPuzzles = mapM_ sudoku [puzzle1, puzzle2, puzzle3, puzzle4, puzzle5, puzzle6]
