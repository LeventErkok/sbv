-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.Newspaper
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Solution to the following puzzle (found at <http://hugopeters.me/posts/15>)
-- which contains 10 questions:
--
-- @
-- a. What is sum of all integer answers?
-- b. How many boolean answers are true?
-- c. Is a the largest number?
-- d. How many integers are equal to me?
-- e. Are all integers positive?
-- f. What is the average of all integers?
-- g. Is d strictly larger than b?
-- h. What is a / h?
-- i. Is f equal to d - b - h * d?
-- j. What is the answer to this question?
-- @
--
-- Note that @j@ is ambiguous: It can be a boolean or an integer. We use
-- the solver to decide what its type should be, so that all the other
-- answers are consistent with that decision.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Puzzles.Newspaper where

import Data.SBV
import Data.SBV.Either

-- | Encoding of the constraints.
puzzle :: Symbolic ()
puzzle = do
    a <- sInteger "a"
    b <- sInteger "b"
    c <- sBool    "c"
    d <- sInteger "d"
    e <- sBool    "e"
    f <- sInteger "f"
    g <- sBool    "g"
    h <- sInteger "h"
    i <- sBool    "i"
    j <- sEither  "j"

    jIsInt <- sBool "jIsInt"

    let ints  intj = [a, b, d, f, h] ++ [fromRight j |     intj]
        bools intj = [c, e, g, i]    ++ [fromLeft  j | not intj]

        choice fn = ite jIsInt (fn True) (fn False)

    -- a. What is sum of all integer answers?
    constrain $ a .== choice (sum . ints)

    -- b. How many boolean answers are true?
    constrain $ b .== choice (sum . map oneIf . bools)

    -- c. Is a the largest number?
    constrain $ c .== (a .== choice (foldr1 smax . ints))

    -- d. How many integers are equal to me?
    constrain $ d .== choice (sum . map (oneIf . (d .==)) . ints)

    -- e. Are all integers positive?
    constrain $ e .== choice (sAll (.> 0) . ints)

    -- f. What is the average of all integers?
    constrain $ f * choice (literal . toInteger . length . ints) .== choice (sum . ints)

    -- g. is d strictly larger than b?
    constrain $ g .== (d .> b)

    -- h. what is a / h?
    constrain $ h * h .== a

    -- i. is f equal to d - b - h * d?
    constrain $ i .== (f .== d - b - h * d)

    -- j. what is the answer to this question?
    constrain $ ite jIsInt (isRight j) (isLeft j)

-- | Print all solutions to the problem. We have:
--
-- >>> solvePuzzle
-- Solution #1:
--   a =         144 :: Integer
--   b =           2 :: Integer
--   c =        True :: Bool
--   d =           2 :: Integer
--   e =       False :: Bool
--   f =          24 :: Integer
--   g =       False :: Bool
--   h =         -12 :: Integer
--   i =        True :: Bool
--   j = Right (-16) :: Either Bool Integer
-- This is the only solution.
solvePuzzle :: IO ()
solvePuzzle = print =<< allSatWith z3{isNonModelVar = (== "jIsInt")} puzzle
