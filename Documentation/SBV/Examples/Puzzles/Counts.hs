-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.Counts
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Consider the sentence:
--
-- @
--    In this sentence, the number of occurrences of 0 is _, of 1 is _, of 2 is _,
--    of 3 is _, of 4 is _, of 5 is _, of 6 is _, of 7 is _, of 8 is _, and of 9 is _.
-- @
--
-- The puzzle is to fill the blanks with numbers, such that the sentence
-- will be correct. There are precisely two solutions to this puzzle, both of
-- which are found by SBV successfully.
--
--  References:
--
--    * Douglas Hofstadter, Metamagical Themes, pg. 27.
--
--    * <http://mathcentral.uregina.ca/mp/archives/previous2002/dec02sol.html>
--
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Puzzles.Counts where

import Data.SBV
import Data.List (sortOn)

-- | We will assume each number can be represented by an 8-bit word, i.e., can be at most 128.
type Count = SWord8

-- | Given a number, increment the count array depending on the digits of the number
count :: Count -> [Count] -> [Count]
count n cnts = ite (n .< 10)
                   (upd n cnts)                           -- only one digit
                   (ite (n .< 100)
                        (upd d1 (upd d2 cnts))            -- two digits
                        (upd d1 (upd d2 (upd d3 cnts))))  -- three digits
  where (r1, d1)   = n  `sQuotRem` 10
        (d3, d2)   = r1 `sQuotRem` 10
        upd d = zipWith inc [0..]
          where inc i c = ite (i .== d) (c+1) c

-- | Encoding of the puzzle. The solution is a sequence of 10 numbers
-- for the occurrences of the digits such that if we count each digit,
-- we find these numbers.
puzzle :: [Count] -> SBool
puzzle cnt = cnt .== last css
  where ones = replicate 10 1  -- all digits occur once to start with
        css  = ones : zipWith count cnt css

-- | Finds all two known solutions to this puzzle. We have:
--
-- >>> counts
-- Solution #1
-- In this sentence, the number of occurrences of 0 is 1, of 1 is 11, of 2 is 2, of 3 is 1, of 4 is 1, of 5 is 1, of 6 is 1, of 7 is 1, of 8 is 1, of 9 is 1.
-- Solution #2
-- In this sentence, the number of occurrences of 0 is 1, of 1 is 7, of 2 is 3, of 3 is 2, of 4 is 1, of 5 is 1, of 6 is 1, of 7 is 2, of 8 is 1, of 9 is 1.
-- Found: 2 solution(s).
counts :: IO ()
counts = do res <- allSat $ puzzle `fmap` mkFreeVars 10
            cnt <- displayModels (sortOn show) disp res
            putStrLn $ "Found: " ++ show cnt ++ " solution(s)."
  where disp n (_, s) = do putStrLn $ "Solution #" ++ show n
                           dispSolution s
        dispSolution :: [Word8] -> IO ()
        dispSolution ns = putStrLn soln
          where soln =  "In this sentence, the number of occurrences"
                     ++  " of 0 is " ++ show (ns !! 0)
                     ++ ", of 1 is " ++ show (ns !! 1)
                     ++ ", of 2 is " ++ show (ns !! 2)
                     ++ ", of 3 is " ++ show (ns !! 3)
                     ++ ", of 4 is " ++ show (ns !! 4)
                     ++ ", of 5 is " ++ show (ns !! 5)
                     ++ ", of 6 is " ++ show (ns !! 6)
                     ++ ", of 7 is " ++ show (ns !! 7)
                     ++ ", of 8 is " ++ show (ns !! 8)
                     ++ ", of 9 is " ++ show (ns !! 9)
                     ++ "."
{- HLint ignore counts "Use head" -}
