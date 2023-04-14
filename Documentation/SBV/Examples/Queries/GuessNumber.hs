-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Queries.GuessNumber
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A simple number-guessing game implementation via queries. Clearly an
-- SMT solver is hardly needed for this problem, but it is a nice demo
-- for the interactive-query programming.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Queries.GuessNumber where

import Data.SBV
import Data.SBV.Control

-- | Use the backend solver to guess the number given as argument.
-- The number is assumed to be between @0@ and @1000@, and we use a simple
-- binary search. Returns the sequence of guesses we performed during
-- the search process.
guess :: Integer -> Symbolic [Integer]
guess input = do g <- sInteger "guess"

                 -- A simple loop to find the value in a query. lb and up
                 -- correspond to the current lower/upper bound we operate in.
                 let loop lb ub sofar = do

                          io $ putStrLn $ "Current bounds: " ++ show (lb, ub)

                          -- Assert the current bound:
                          constrain $ g .>= literal lb
                          constrain $ g .<= literal ub

                          -- Issue a check-sat
                          cs <- checkSat
                          case cs of
                            Unk    -> error "Too bad, solver said Unknown.." -- Won't really happen
                            DSat{} -> error "Unexpected delta-sat result.."  -- Won't really happen
                            Unsat  ->
                                   -- This cannot happen! If it does, the input was
                                   -- not properly constrainted. Note that we found this
                                   -- by getting an Unsat, not by checking the value!
                                   error $ unlines [ "There's no solution!"
                                                   , "Guess sequence: " ++ show (reverse sofar)
                                                   ]
                            Sat    -> do gv <- getValue g
                                         case gv `compare` input of
                                           EQ -> -- Got it, return:
                                                 return (reverse (gv : sofar))
                                           LT -> -- Solver guess is too small, increase the lower bound:
                                                 loop ((lb+1) `max` (lb + (input - lb) `div` 2)) ub (gv : sofar)
                                           GT -> -- Solver guess is too big, decrease the upper bound:
                                                 loop lb ((ub-1) `min` (ub - (ub - input) `div` 2)) (gv : sofar)

                 -- Start the search
                 query $ loop 0 1000 []

-- | Play a round of the game, making the solver guess the secret number 42.
-- Note that you can generate a random-number and make the solver guess it too!
-- We have:
--
-- >>> play
-- Current bounds: (0,1000)
-- Current bounds: (21,1000)
-- Current bounds: (31,1000)
-- Current bounds: (36,1000)
-- Current bounds: (39,1000)
-- Current bounds: (40,1000)
-- Current bounds: (41,1000)
-- Current bounds: (42,1000)
-- Solved in: 8 guesses:
--   8 21 31 36 39 40 41 42
play :: IO ()
play = do gs <- runSMT (guess 42)
          putStrLn $ "Solved in: " ++ show (length gs) ++ " guesses:"
          putStrLn $ "  " ++ unwords (map show gs)
