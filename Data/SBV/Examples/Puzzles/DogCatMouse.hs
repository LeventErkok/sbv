-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Puzzles.DogCatMouse
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Puzzle:
--   Spend exactly 100 dollars and buy exactly 100 animals.
--   Dogs cost 15 dollars, cats cost 1 dollar, and mice cost 25 cents each.
--   You have to buy at least one of each.
--   How many of each should you buy?
-----------------------------------------------------------------------------

module Data.SBV.Examples.Puzzles.DogCatMouse where

import Data.SBV

-- | Prints the only solution:
--
-- >>> puzzle
-- Solution #1:
--   dog = 3 :: SInteger
--   cat = 41 :: SInteger
--   mouse = 56 :: SInteger
-- This is the only solution.
puzzle :: IO AllSatResult
puzzle = allSat $ do
           [dog, cat, mouse] <- sIntegers ["dog", "cat", "mouse"]
           solve [ dog   .>= 1                                   -- at least one dog
                 , cat   .>= 1                                   -- at least one cat
                 , mouse .>= 1                                   -- at least one mouse
                 , dog + cat + mouse .== 100                     -- buy precisely 100 animals
                 , 1500 * dog + 100 * cat + 25 * mouse .== 10000 -- spend exactly 100 dollars (use cents since we don't have fractions)
                 ]
