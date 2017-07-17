-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Queries.AllSat
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- When we would like to find all solutions to a problem, we can query the
-- solver repeatedly, telling it to give us a new model each time. SBV already
-- provides 'allSat' that precisely does this. However, this example demonstrates
-- how the query mode can be used to achieve the same, and can also incorporate
-- extra conditions with easy as we walk through solutions.
-----------------------------------------------------------------------------

module Data.SBV.Examples.Queries.AllSat where

import Data.SBV
import Data.SBV.Control

import Data.List

-- | Find all solutions to @x + y .== 10@ for positive @x@ and @y@, but at each
-- iteration we would like to ensure that the value of @x@ we get is at least twice as large as
-- the previous one. This is rather silly, but demonstrates how we can dynamically
-- query the result and put in new constraints based on those.
goodSum :: Symbolic [(Integer, Integer)]
goodSum = do x <- sInteger "x"
             y <- sInteger "y"

             -- constrain positive and sum:
             constrain $ x .>= 0
             constrain $ y .>= 0
             constrain $ x + y .== 10

             -- Capture the "next" solution function:
             let next i sofar = do
                    io $ putStrLn $ "Iteration: " ++ show (i :: Int)

                    cs <- checkSat
                    case cs of
                      Unk   -> error "Too bad, solver said unknown.." -- Won't happen
                      Unsat -> do io $ putStrLn "No other solution!"
                                  return sofar

                      Sat   -> do xv <- getValue x
                                  yv <- getValue y

                                  io $ putStrLn $ "Current solution is: " ++ show (xv, yv)

                                  -- For next iteration: Put in constraints outlawing the current one:
                                  -- Note that we do *not* put these separately, as we do want
                                  -- to allow repetition on one value if the other is different!
                                  constrain $   x ./= literal xv
                                            ||| y ./= literal yv

                                  -- Also request @x@ to be twice as large, for demo purposes:
                                  constrain $ x .>= 2 * literal xv

                                  -- loop around!
                                  next (i+1) ((xv, yv) : sofar)

             -- Go into query mode and execute the loop:
             query $ do io $ putStrLn "Starting the all-sat engine!"
                        next 1 []

-- | Run the query. We have:
--
-- >>> demo
-- Starting the all-sat engine!
-- Iteration: 1
-- Current solution is: (0,10)
-- Iteration: 2
-- Current solution is: (1,9)
-- Iteration: 3
-- Current solution is: (2,8)
-- Iteration: 4
-- Current solution is: (4,6)
-- Iteration: 5
-- Current solution is: (8,2)
-- Iteration: 6
-- No other solution!
-- [(0,10),(1,9),(2,8),(4,6),(8,2)]
demo :: IO ()
demo = do ss <- runSMT goodSum
          print $ sort ss
