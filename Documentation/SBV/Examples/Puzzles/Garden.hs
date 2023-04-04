-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.Garden
-- Copyright : (c) Levent Erkok
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
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Puzzles.Garden where

import Data.SBV

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
puzzle :: ConstraintSet
puzzle = do n <- sInteger "N"

            let valid = validPick n

            -- Each color is represented:
            constrain $ \(Exists ef1) (Exists ef2) (Exists ef3) ->
               valid ef1 ef2 ef3 .&& map col [ef1, ef2, ef3] .== [sRed, sYellow, sBlue]

            -- Pick any three, at least one is Red, one is Yellow, one is Blue
            constrain $ \(Forall af1) (Forall af2) (Forall af3) ->
                let atLeastOne c = count c [af1, af2, af3] .>= 1
                in valid af1 af2 af3 .=> atLeastOne Red .&& atLeastOne Yellow .&& atLeastOne Blue

-- | Solve the puzzle. We have:
--
-- >>> flowerCount
-- Solution #1:
--   N = 3 :: Integer
-- This is the only solution.
--
-- So, a garden with 3 flowers is the only solution. (Note that we simply skip
-- over the prefix existentials and the assignments to uninterpreted function 'col'
-- for model purposes here, as they don't represent a different solution.)
flowerCount :: IO ()
flowerCount = print =<< allSatWith z3{allSatTrackUFs=False} puzzle
