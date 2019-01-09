-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.Garden
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- The origin of this puzzle is Raymond Smullyan's "The Flower Garden" riddle:
--
--     In a certain flower garden, each flower was either red, yellow,
--     or blue, and all three colors were represented. A statistician
--     once visited the garden and made the observation that whatever
--     three flowers you picked, at least one of them was bound to be red.
--     A second statistician visited the garden and made the observation
--     that whatever three flowers you picked, at least one was bound to
--     be yellow.
--
--     Two logic students heard about this and got into an argument.
--     The first student said: “It therefore follows that whatever
--     three flowers you pick, at least one is bound to be blue, doesn’t
--     it?” The second student said: “Of course not!”
--
--     Which student was right, and why?
--
-- We slightly modify the puzzle. Assuming the first student is right, we use
-- SBV to show that the garden must contain exactly 3 flowers. In any other
-- case, the second student would be right.
------------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}

module Documentation.SBV.Examples.Puzzles.Garden where

import Data.SBV
import Data.List(isSuffixOf)

-- | Colors of the flowers
data Color = Red | Yellow | Blue

-- | Make 'Color' a symbolic value.
mkSymbolicEnumeration ''Color

-- | Represent flowers by symbolic integers
type Flower = SInteger

-- | The uninterpreted function 'col' assigns a color to each flower.
col :: Flower -> SBV Color
col = uninterpret "col"

-- | Describe a valid pick of three flowers @i@, @j@, @k@, assuming
-- we have @n@ flowers to start with. Essentially the numbers should
-- be within bounds and distinct.
validPick :: SInteger -> Flower -> Flower -> Flower -> SBool
validPick n i j k = distinct [i, j, k] .&& sAll ok [i, j, k]
  where ok x = inRange x (1, n)

-- | Count the number of flowers that occur in a given set of flowers.
count :: Color -> [Flower] -> SInteger
count c fs = sum [ite (col f .== literal c) 1 0 | f <- fs]

-- | Smullyan's puzzle.
puzzle :: Goal
puzzle = do n <- sInteger "N"

            let valid = validPick n

            -- Declare three existential flowers. We name these with
            -- the suffix "_modelIgnore" as we don't consider variations
            -- on them to be interesting for model construction purposes.
            -- We'll use the 'isNonModelVar' parameter to ignore them
            -- for that purpose.
            ef1 <- exists "ef1_modelIgnore"
            ef2 <- exists "ef2_modelIgnore"
            ef3 <- exists "ef3_modelIgnore"

            -- Declare three universal flowers to aid in encoding the
            -- statements made by students.
            af1 <- forall "af1"
            af2 <- forall "af2"
            af3 <- forall "af3"

            -- Each color is represented:
            constrain $ valid ef1 ef2 ef3
            constrain $ map col [ef1, ef2, ef3] .== map literal [Red, Yellow, Blue]

            -- Pick any three, at least one is Red
            constrain $ valid af1 af2 af3 .=> count Red    [af1, af2, af3] .>= 1

            -- Pick any three, at least one is Yellow
            constrain $ valid af1 af2 af3 .=> count Yellow [af1, af2, af3] .>= 1

            -- Pick any three, at least one is Blue
            constrain $ valid af1 af2 af3 .=> count Blue   [af1, af2, af3] .>= 1

-- | Solve the puzzle. We have:
--
-- >>> flowerCount
-- Solution #1:
--   N = 3 :: Integer
-- This is the only solution. (Unique up to prefix existentials.)
--
-- So, a garden with 3 flowers is the only solution. (Note that we simply skip
-- over the prefix existentials for model purposes here, as they don't represent
-- a different solution.)
flowerCount :: IO ()
flowerCount = print =<< allSatWith z3{isNonModelVar = ("_modelIgnore" `isSuffixOf`)} puzzle
