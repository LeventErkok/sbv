-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.HexPuzzle
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- We're given a board, with 19 hexagon cells. The cells are arranged as follows:
--
-- @
--                     01  02  03
--                   04  05  06  07
--                 08  09  10  11  12
--                   13  14  15  16
--                     17  18  19
-- @
--
--   - Each cell has a color, one of @BLACK@, @BLUE@, @GREEN@, or @RED@.
--
--   - At each step, you get to press one of the center buttons. That is,
--     one of 5, 6, 9, 10, 11, 14, or 15.
--
--   - Pressing a button that is currently colored @BLACK@ has no effect.
--
--   - Otherwise (i.e., if the pressed button is not @BLACK@), then colors
--     rotate clockwise around that button. For instance if you press 15
--     when it is not colored @BLACK@, then 11 moves to 16, 16 moves to 19,
--     19 moves to 18, 18 moves to 14, 14 moves to 10, and 10 moves to 11.
--
--   - Note that by "move," we mean the colors move: We still refer to the buttons
--     with the same number after a move.
--
-- You are given an initial board coloring, and a final one. Your goal is
-- to find a minimal sequence of button presses that will turn the original board
-- to the final one.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Puzzles.HexPuzzle where

import Data.SBV
import Data.SBV.Control

-- | Colors we're allowed
data Color = Black | Blue | Green | Red

-- | Make 'Color' a symbolic value.
mkSymbolicEnumeration ''Color

-- | Use 8-bit words for button numbers, even though we only have 1 to 19.
type Button  = Word8

-- | Symbolic version of button.
type SButton = SBV Button

-- | The grid is an array mapping each button to its color.
type Grid = SArray Button Color

-- | Given a button press, and the current grid, compute the next grid.
-- If the button is "unpressable", i.e., if it is not one of the center
-- buttons or it is currently colored black, we return the grid unchanged.
next :: SButton -> Grid -> Grid
next b g = ite (readArray g b .== sBlack) g
         $ ite (b .==  5)                        (rot [ 1,  2,  6, 10,  9,  4])
         $ ite (b .==  6)                        (rot [ 2,  3,  7, 11, 10,  5])
         $ ite (b .==  9)                        (rot [ 4,  5, 10, 14, 13,  8])
         $ ite (b .== 10)                        (rot [ 5,  6, 11, 15, 14,  9])
         $ ite (b .== 11)                        (rot [ 6,  7, 12, 16, 15, 10])
         $ ite (b .== 14)                        (rot [ 9, 10, 15, 18, 17, 13])
         $ ite (b .== 15)                        (rot [10, 11, 16, 19, 18, 14]) g
  where rot xs = foldr (\(i, c) a -> writeArray a (literal i) c) g (zip new cur)
          where cur = map (readArray g . literal) xs
                new = drop 1 xs ++ take 1 xs

-- | Iteratively search at increasing depths of button-presses to see if we can
-- transform from the initial board position to a final board position.
search :: [Color] -> [Color] -> IO ()
search initial final = runSMT $ do emptyGrid :: Grid <- newArray "emptyGrid" (Just sBlack)
                                   let initGrid = foldr (\(i, c) a -> writeArray a (literal i) (literal c)) emptyGrid (zip [1..] initial)
                                   query $ loop (0 :: Int) initGrid []

  where loop i g sofar = do io $ putStrLn $ "Searching at depth: " ++ show i

                            -- Go into a new context, and see if we've reached a solution:
                            push 1
                            constrain $ map (readArray g . literal) [1..19] .== map literal final
                            cs <- checkSat

                            case cs of
                              Unk    -> error $ "Solver said Unknown, depth: " ++ show i

                              DSat{} -> error $ "Solver returned a delta-satisfiable result, depth: " ++ show i

                              Unsat  -> do -- It didn't work out. Pop and try again with one more move:
                                           pop 1
                                           b <- freshVar ("press_" ++ show i)
                                           constrain $ b `sElem` map literal [5, 6, 9, 10, 11, 14, 15]
                                           loop (i+1) (next b g) (sofar ++ [b])

                              Sat    -> do vs <- mapM getValue sofar
                                           io $ putStrLn $ "Found: " ++ show vs
                                           findOthers sofar vs

        findOthers vs = go
                where go curVals = do constrain $ sOr $ zipWith (\v c -> v ./= literal c) vs curVals
                                      cs <- checkSat
                                      case cs of
                                       Unk    -> error "Unknown!"
                                       DSat{} -> error "Delta-sat!"
                                       Unsat  -> io $ putStrLn "There are no more solutions."
                                       Sat    -> do newVals <- mapM getValue vs
                                                    io $ putStrLn $ "Found: " ++ show newVals
                                                    go newVals

-- | A particular example run. We have:
--
-- >>> example
-- Searching at depth: 0
-- Searching at depth: 1
-- Searching at depth: 2
-- Searching at depth: 3
-- Searching at depth: 4
-- Searching at depth: 5
-- Searching at depth: 6
-- Found: [10,10,11,9,14,6]
-- Found: [10,10,9,11,14,6]
-- There are no more solutions.
example :: IO ()
example = search initBoard finalBoard
   where initBoard  = [Black, Black, Black, Red, Blue, Green, Red, Black, Green, Green, Green, Black, Red, Green, Green, Red, Black, Black, Black]
         finalBoard = [Black, Red, Black, Black, Green, Green, Black, Red, Green, Blue, Green, Red, Black, Green, Green, Black, Black, Red, Black]
