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

-- | Use 16-bit words to represent the counts, much larger than we actually need, but no harm.
type Count = SWord16

-- | Codes the puzzle statement, more or less directly using SBV.
puzzle :: Count -> Count -> Count -> SBool
puzzle dog cat mouse =
         dog   .>= 1 &&& dog   .<= 98                  -- at least one dog and at most 98
    &&&  cat   .>= 1 &&& cat   .<= 98                  -- ditto for cats
    &&&  mouse .>= 1 &&& mouse .<= 98                  -- ditto for mice
    &&&  dog + cat + mouse .== 100                     -- buy precisely 100 animals
    &&&  1500 * dog + 100 * cat + 25 * mouse .== 10000 -- spend exactly 100 dollars (use cents since we don't have fractions)

-- | prints the only solution:
--
-- @
--     dog = 3 :: SWord16
--     cat = 41 :: SWord16
--     mouse = 56 :: SWord16
-- @
solve :: IO ()
solve = print =<< allSat (forAll ["dog", "cat", "mouse"] puzzle)
