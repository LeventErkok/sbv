-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.Tower
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Solves the tower puzzle, <http://www.chiark.greenend.org.uk/%7Esgtatham/puzzles/js/towers.html>.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Puzzles.Tower where

import Control.Monad
import Data.Array hiding (inRange)
import Data.SBV
import Data.SBV.Control

-------------------------------------------------------------------
-- * Modeling Towers
-------------------------------------------------------------------

-- | Count of visible towers as an array.
type Count a = Array Integer a

-- | The grid itself. The indexes are tuples, first coordinate increases as you go from
-- left to right, and the second increases as you go from top to bottom.
type Grid a = Array (Integer, Integer) a

-- | The problem has 4 counts, from top, left, bottom, and right. And the grid itself.
type Problem a = (Count a, Count a, Count a, Count a, Grid a)

-- | Example problem. Encodes:
--
-- @
--     - - 3 - - 4
--   -     2       5
--   -   2         -
--   4             -
--   2             -
--   -             2
--   3             -
--     - - 3 4 - -
-- @
problem :: Problem (Maybe Integer)
problem = (top, left, bot, right, grid)
  where build ix es = accumArray (\_ a -> a) Nothing ix [(i, Just v) | (i, v) <- es]

        top   = build  (1, 6)          [(3, 3), (6, 4)]
        left  = build  (1, 6)          [(3, 4), (4, 2), (6, 3)]
        bot   = build  (1, 6)          [(3, 3), (4, 4)]
        right = build  (1, 6)          [(1, 5), (5, 2)]
        grid  = build ((1, 1), (6, 6)) [((3, 1), 2), ((2, 2), 2)]

-- | Given a concrete partial board, turn it into a symbolic board, by filling in the
-- empty cells with symbolic variables.
symProblem :: Problem (Maybe Integer) -> Symbolic (Problem SInteger)
symProblem (t, l, b, r, g) = (,,,,) <$> fill t <*> fill l <*> fill b <*> fill r <*> fill g
 where fill :: Traversable f => f (Maybe Integer) -> Symbolic (f SInteger)
       fill = mapM (maybe free_ (pure . literal))

-------------------------------------------------------------------
-- * Counting visible towers
-------------------------------------------------------------------

-- | Given a list of tower heights, count the number of visible ones in the given order.
-- We simply keep track of the tallest we have seen so far, and increment the count for
-- each tower we see if it's taller than the tallest seen so far.
visible :: [SInteger] -> SInteger
visible = go 0 0
 where go _            visibleSofar []     = visibleSofar
       go tallestSofar visibleSofar (x:xs) = go (tallestSofar `smax` x)
                                                (ite (x .> tallestSofar) (1 + visibleSofar) visibleSofar)
                                                xs

-------------------------------------------------------------------
-- * Building constraints
-------------------------------------------------------------------

-- | Build the constraints for a given problem. We scan the elements and add the required
-- visibility counts for each row and column, viewed both in the correct order and in the backwards order.
tower :: Problem SInteger -> Symbolic ()
tower (top, left, bot, right, grid) = do
  let (minX, maxX) = bounds top
      (minY, maxY) = bounds left

  -- Constraints from top and bottom
  forM_ [minX .. maxX] $ \x -> do
      let reqT = top ! x
          reqB = bot ! x
          elts = [grid ! (x, y) | y <- [minY .. maxY]]
      mapM_ (\e -> constrain (inRange e (literal 1, literal maxY))) elts
      constrain $ distinct elts
      constrain $ reqT .== visible elts
      constrain $ reqB .== visible (reverse elts)

  -- Constraints from left and right
  forM_ [minY .. maxY] $ \y -> do
      let reqL = left  ! y
          reqR = right ! y
          elts = [grid ! (x, y) | x <- [minX .. maxX]]
      mapM_ (\e -> constrain (inRange e (literal 1, literal maxX))) elts
      constrain $ distinct elts
      constrain $ reqL .== visible elts
      constrain $ reqR .== visible (reverse elts)

  pure ()

-------------------------------------------------------------------
-- * Example run
-------------------------------------------------------------------

-- | Solve the puzzle descibed above. We get:
--
-- >>> example
--   1 2 3 2 2 4
-- 1 6 5 2 4 3 1 5
-- 3 3 2 5 6 1 4 2
-- 4 2 4 1 5 6 3 2
-- 2 5 3 6 1 4 2 3
-- 2 1 6 4 3 2 5 2
-- 3 4 1 3 2 5 6 1
--   3 2 3 4 2 1
example :: IO ()
example = runSMT $ do
        sp <- symProblem problem
        tower sp
        query $ do cs <- checkSat
                   case cs of
                     Unsat -> io $ putStrLn "Unsolvable"
                     Sat   -> display sp
                     _     -> error $ "Unexpected result: " ++ show cs
 where display :: Problem SInteger -> Query ()
       display (top, left, bot, right, grid) = do
          let (minX, maxX) = bounds top
              (minY, maxY) = bounds left

              sh x = do vx <- getValue x
                        io $ putStr $ show vx ++ " "

          io $ putStr "  "
          forM_ [minX .. maxX] $ \x -> sh (top ! x)
          io $ putStrLn ""

          forM_ [minY .. maxY] $ \y -> do
             sh (left ! y)
             forM_ [minX .. maxX] $ \x -> do
               sh (grid ! (x, y))
             sh (right ! y)
             io $ putStrLn ""

          io $ putStr "  "
          forM_ [minX .. maxX] $ \x -> sh (bot ! x)
          io $ putStrLn ""
