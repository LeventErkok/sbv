-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.DogCatMouse
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Puzzle:
--   Spend exactly 100 dollars and buy exactly 100 animals.
--   Dogs cost 15 dollars, cats cost 1 dollar, and mice cost 25 cents each.
--   You have to buy at least one of each.
--   How many of each should you buy?
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Puzzles.DogCatMouse where

import Data.SBV

-- | Prints the only solution:
--
-- >>> puzzle
-- Solution #1:
--   dog   =  3 :: Integer
--   cat   = 41 :: Integer
--   mouse = 56 :: Integer
-- This is the only solution.
puzzle :: IO AllSatResult
puzzle = allSat $ do
           [dog, cat, mouse] <- sIntegers ["dog", "cat", "mouse"]
           solve [ dog   .>= 1                                           -- at least one dog
                 , cat   .>= 1                                           -- at least one cat
                 , mouse .>= 1                                           -- at least one mouse
                 , dog + cat + mouse .== 100                             -- buy precisely 100 animals
                 , 15 `per` dog + 1 `per` cat + 0.25 `per` mouse .== 100 -- spend exactly 100 dollars
                 ]
  where p `per` q = p * (sFromIntegral q :: SReal)
