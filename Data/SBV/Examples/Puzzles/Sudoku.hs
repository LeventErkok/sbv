-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Puzzles.Sudoku
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- The Sudoku solver, quintessential SMT solver example!
-----------------------------------------------------------------------------

module Data.SBV.Examples.Puzzles.Sudoku where

import Data.List  (transpose)
import Data.Maybe (fromJust)

import Data.SBV

-------------------------------------------------------------------
-- * Modeling Sudoku
-------------------------------------------------------------------
-- | A row is a sequence of 8-bit words, too large indeed for representing 1-9, but does not harm
type Row   = [SWord8]

-- | A Sudoku board is a sequence of 9 rows
type Board = [Row]

-- | Given a series of elements, make sure they are all different
-- and they all are numbers between 1 and 9
check :: [SWord8] -> SBool
check grp = bAnd $ allDifferent grp : map rangeFine grp
  where rangeFine x = x .> 0 &&& x .<= 9

-- | Given a full Sudoku board, check that it is valid
valid :: Board -> SBool
valid rows = bAnd $ literal sizesOK : map check (rows ++ columns ++ squares)
  where sizesOK = length rows == 9 && all (\r -> length r == 9) rows
        columns = transpose rows
        regions = transpose [chunk 3 row | row <- rows]
        squares = [concat sq | sq <- chunk 3 (concat regions)]
        chunk :: Int -> [a] -> [[a]]
        chunk _ [] = []
        chunk i xs = let (f, r) = splitAt i xs in f : chunk i r

-- | A puzzle is a pair: First is the number of missing elements, second
-- is a function that given that many elements returns the final board.
type Puzzle = (Int, [SWord8] -> Board)

-------------------------------------------------------------------
-- * Solving Sudoku puzzles
-------------------------------------------------------------------

-- | Solve a given puzzle and print the results
solve :: Puzzle -> IO ()
solve p@(i, f) = do putStrLn "Solving the puzzle.."
                    SatResult res <- sat $ mapM (const free_) [1..i] >>= output . valid . f
                    dispSolution p (getModel res)

-- | Helper function to display results nicely, not really needed, but helps presentation
dispSolution :: Puzzle -> [Word8] -> IO ()
dispSolution (i, f) fs
  | lmod /= i = error $ "Impossible! Backend solver returned " ++ show lmod ++ " values, was expecting: " ++ show i
  | True      = do putStrLn "Final board:"
                   mapM_ printRow final
                   putStrLn $ "Valid Check: " ++ show (valid final)
                   putStrLn "Done."
  where lmod = length fs
        final = f (map literal fs)
        printRow r = putStr "   " >> mapM_ (\x -> putStr (show (fromJust (unliteral x)) ++ " ")) r >> putStrLn ""

-- | Find all solutions to a puzzle
solveAll :: Puzzle -> IO ()
solveAll p@(i, f) = do putStrLn "Finding all solutions.."
                       res <- allSat $ mapM (const free_) [1..i] >>= output . valid . f
                       cnt <- displayModels disp res
                       putStrLn $ "Found: " ++ show cnt ++ " solution(s)."
   where disp n s = do putStrLn $ "Solution #" ++ show n
                       dispSolution p s

-------------------------------------------------------------------
-- * Example boards
-------------------------------------------------------------------

-- | Find an arbitrary good board
puzzle0 :: Puzzle
puzzle0 = (81, f)
  where f   [ a1, a2, a3, a4, a5, a6, a7, a8, a9,
              b1, b2, b3, b4, b5, b6, b7, b8, b9,
              c1, c2, c3, c4, c5, c6, c7, c8, c9,
              d1, d2, d3, d4, d5, d6, d7, d8, d9,
              e1, e2, e3, e4, e5, e6, e7, e8, e9,
              f1, f2, f3, f4, f5, f6, f7, f8, f9,
              g1, g2, g3, g4, g5, g6, g7, g8, g9,
              h1, h2, h3, h4, h5, h6, h7, h8, h9,
              i1, i2, i3, i4, i5, i6, i7, i8, i9 ]
         = [ [a1, a2, a3, a4, a5, a6, a7, a8, a9],
             [b1, b2, b3, b4, b5, b6, b7, b8, b9],
             [c1, c2, c3, c4, c5, c6, c7, c8, c9],
             [d1, d2, d3, d4, d5, d6, d7, d8, d9],
             [e1, e2, e3, e4, e5, e6, e7, e8, e9],
             [f1, f2, f3, f4, f5, f6, f7, f8, f9],
             [g1, g2, g3, g4, g5, g6, g7, g8, g9],
             [h1, h2, h3, h4, h5, h6, h7, h8, h9],
             [i1, i2, i3, i4, i5, i6, i7, i8, i9] ]
        f _ = error "puzzle0 needs exactly 81 elements!"

-- | A random puzzle, found on the internet..
puzzle1 :: Puzzle
puzzle1 = (49, f)
  where f   [ a1,     a3, a4, a5, a6, a7,     a9,
              b1, b2, b3,             b7, b8, b9,
                  c2,     c4, c5, c6,     c8,
                      d3,     d5,     d7,
              e1, e2,     e4, e5, e6,     e8, e9,
                      f3,     f5,     f7,
                  g2,     g4, g5, g6,     g8,
              h1, h2, h3,             h7, h8, h9,
              i1,     i3, i4, i5, i6, i7,     i9 ]
         = [ [a1,  6, a3, a4, a5, a6, a7,  1, a9],
             [b1, b2, b3,  6,  5,  1, b7, b8, b9],
             [ 1, c2,  7, c4, c5, c6,  6, c8,  2],
             [ 6,  2, d3,  3, d5,  5, d7,  9,  4],
             [e1, e2,  3, e4, e5, e6,  2, e8, e9],
             [ 4,  8, f3,  9, f5,  7, f7,  3,  6],
             [ 9, g2,  6, g4, g5, g6,  4, g8,  8],
             [h1, h2, h3,  7,  9,  4, h7, h8, h9],
             [i1,  5, i3, i4, i5, i6, i7,  7, i9] ]
        f _ = error "puzzle1 needs exactly 49 elements!"

-- | Another random puzzle, found on the internet..
puzzle2 :: Puzzle
puzzle2 = (55, f)
  where f   [     a2,     a4, a5, a6, a7,     a9,
              b1, b2,     b4,         b7, b8, b9,
              c1,     c3, c4, c5, c6, c7, c8, c9,
                  d2, d3, d4,             d8, d9,
              e1,     e3,     e5,     e7,     e9,
              f1, f2,             f6, f7, f8,
              g1, g2, g3, g4, g5, g6, g7,     g9,
              h1, h2, h3,         h6,     h8, h9,
              i1,     i3, i4, i5, i6,     i8     ]
         = [ [ 1, a2,  3, a4, a5, a6, a7,  8, a9],
             [b1, b2,  6, b4,  4,  8, b7, b8, b9],
             [c1,  4, c3, c4, c5, c6, c7, c8, c9],
             [ 2, d2, d3, d4,  9,  6,  1, d8, d9],
             [e1,  9, e3,  8, e5,  1, e7,  4, e9],
             [f1, f2,  4,  3,  2, f6, f7, f8,  8],
             [g1, g2, g3, g4, g5, g6, g7,  7, g9],
             [h1, h2, h3,  1,  5, h6,  4, h8, h9],
             [i1,  6, i3, i4, i5, i6,  2, i8,  3] ]
        f _ = error "puzzle2 needs exactly 55 elements!"

-- | Another random puzzle, found on the internet..
puzzle3 :: Puzzle
puzzle3 = (56, f)
  where f   [     a2, a3, a4,     a6,     a8, a9,
                  b2,     b4, b5, b6, b7, b8, b9,
              c1, c2, c3, c4,     c6, c7,     c9,
              d1,     d3,     d5,     d7,     d9,
                  e2, e3, e4,     e6, e7, e8,
              f1,     f3,     f5,     f7,     f9,
              g1,     g3, g4,     g6, g7, g8, g9,
              h1, h2, h3, h4, h5, h6,     h8,
              i1, i2,     i4,     i6, i7, i8     ]
         = [ [ 6, a2, a3, a4,  1, a6,  5, a8, a9],
             [ 8, b2,  3, b4, b5, b6, b7, b8, b9],
             [c1, c2, c3, c4,  6, c6, c7,  2, c9],
             [d1,  3, d3,  1, d5,  8, d7,  9, d9],
             [ 1, e2, e3, e4,  9, e6, e7, e8,  4],
             [f1,  5, f3,  2, f5,  3, f7,  1, f9],
             [g1,  7, g3, g4,  3, g6, g7, g8, g9],
             [h1, h2, h3, h4, h5, h6,  3, h8,  6],
             [i1, i2,  4, i4,  5, i6, i7, i8,  9] ]
        f _ = error "puzzle3 needs exactly 56 elements!"

-- | According to the web, this is the toughest 
-- sudoku puzzle ever.. It even has a name: Al Escargot:
-- <http://zonkedyak.blogspot.com/2006/11/worlds-hardest-sudoku-puzzle-al.html>
puzzle4 :: Puzzle
puzzle4 = (58, f)
  where f   [     a2, a3, a4, a5,     a7,     a9,
              b1,     b3, b4,     b6, b7, b8,
              c1, c2,         c5, c6,     c8, c9,
              d1, d2,         d5, d6,     d8, d9,
              e1,     e3, e4,     e6, e7, e8,
                  f2, f3, f4, f5,     f7, f8, f9,
                  g2, g3, g4, g5, g6, g7,     g9,
              h1,     h3, h4, h5, h6, h7, h8,
              i1, i2,     i4, i5, i6,     i8, i9 ]
         = [ [ 1, a2, a3, a4, a5,  7, a7,  9, a9],
             [b1,  3, b3, b4,  2, b6, b7, b8,  8],
             [c1, c2,  9,  6, c5, c6,  5, c8, c9],
             [d1, d2,  5,  3, d5, d6,  9, d8, d9],
             [e1,  1, e3, e4,  8, e6, e7, e8,  2],
             [ 6, f2, f3, f4, f5,  4, f7, f8, f9],
             [ 3, g2, g3, g4, g5, g6, g7,  1, g9],
             [h1,  4, h3, h4, h5, h6, h7, h8,  7],
             [i1, i2,  7, i4, i5, i6,  3, i8, i9] ]
        f _ = error "puzzle4 needs exactly 58 elements!"

-- | This one has been called diabolical, apparently
puzzle5 :: Puzzle
puzzle5 = (53, f)
  where f   [ a1,     a3,     a5, a6,         a9,
              b1,         b4, b5,     b7,     b9,
                  c2,     c4, c5, c6, c7, c8, c9,
              d1, d2,     d4,     d6, d7, d8,
              e1, e2, e3,     e5,     e7, e8, e9,
                  f2, f3, f4,     f6,     f8, f9,
              g1, g2, g3, g4, g5, g6,     g8,
              h1,     h3,     h5, h6,         h9,
              i1,         i4, i5,     i7,     i9 ]
         = [ [a1,  9, a3,  7, a5, a6,  8,  6, a9],
             [b1,  3,  1, b4, b5,  5, b7,  2, b9],
             [ 8, c2,  6, c4, c5, c6, c7, c8, c9],
             [d1, d2,  7, d4,  5, d6, d7, d8,  6],
             [e1, e2, e3,  3, e5,  7, e7, e8, e9],
             [ 5, f2, f3, f4,  1, f6,  7, f8, f9],
             [g1, g2, g3, g4, g5, g6,  1, g8,  9],
             [h1,  2, h3,  6, h5, h6,  3,  5, h9],
             [i1,  5,  4, i4, i5,  8, i7,  7, i9] ]
        f _ = error "puzzle5 needs exactly 53 elements!"

-- | The following is nefarious according to
-- <http://haskell.org/haskellwiki/Sudoku>
puzzle6 :: Puzzle
puzzle6 = (64, f)
  where f   [ a1, a2, a3, a4,     a6, a7,     a9,
              b1,     b3, b4, b5, b6, b7, b8, b9,
              c1, c2,     c4, c5, c6, c7, c8, c9,
              d1,     d3, d4, d5, d6,     d8,
                  e2, e3, e4,     e6, e7, e8, e9,
              f1, f2, f3, f4, f5, f6,     f8, f9,
              g1, g2,         g5,     g7, g8, g9,
                  h2, h3,     h5, h6,     h8, h9,
              i1, i2, i3, i4, i5, i6, i7,     i9  ]
         = [ [a1, a2, a3, a4,  6, a6, a7,  8, a9],
             [b1,  2, b3, b4, b5, b6, b7, b8, b9],
             [c1, c2,  1, c4, c5, c6, c7, c8, c9],
             [d1,  7, d3, d4, d5, d6,  1, d8,  2],
             [ 5, e2, e3, e4,  3, e6, e7, e8, e9],
             [f1, f2, f3, f4, f5, f6,  4, f8, f9],
             [g1, g2,  4,  2, g5,  1, g7, g8, g9],
             [ 3, h2, h3,  7, h5, h6,  6, h8, h9],
             [i1, i2, i3, i4, i5, i6, i7,  5, i9] ]
        f _ = error "puzzle6 needs exactly 64 elements!"

-- | Solve them all, this takes a fraction of a second to run for each case
allPuzzles :: IO ()
allPuzzles = mapM_ solve [puzzle0, puzzle1, puzzle2, puzzle3, puzzle4, puzzle5, puzzle6]
