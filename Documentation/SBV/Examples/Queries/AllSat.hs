-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Queries.AllSat
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- When we would like to find all solutions to a problem, we can query the
-- solver repeatedly, telling it to give us a new model each time. SBV already
-- provides 'Data.SBV.allSat' that precisely does this. However, this example demonstrates
-- how the query mode can be used to achieve the same, and can also incorporate
-- extra conditions with easy as we walk through solutions.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Queries.AllSat where

import Data.SBV
import Data.SBV.Control

-- | Find all solutions to @x + y .== 10@ for positive @x@ and @y@.
-- This is rather silly to do in the query mode as `allSat` can do
-- this automatically, but it demonstrates how we can dynamically
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
                    io $ putStrLn $ "Iteration: " ++ show (i :: Integer)

                    -- Using a check-sat assuming, we force the solver to walk through
                    -- the entire range of x's
                    cs <- checkSatAssuming [x .== literal (i-1)]

                    case cs of
                      Unk    -> error "Too bad, solver said unknown.." -- Won't happen
                      DSat{} -> error "Unexpected dsat result.."       -- Won't happen
                      Unsat  -> do io $ putStrLn "No other solution!"
                                   return $ reverse sofar

                      Sat    -> do xv <- getValue x
                                   yv <- getValue y

                                   io $ putStrLn $ "Current solution is: " ++ show (xv, yv)

                                   -- For next iteration: Put in constraints outlawing the current one:
                                   -- Note that we do *not* put these separately, as we do want
                                   -- to allow repetition on one value if the other is different!
                                   constrain $   x ./= literal xv
                                             .|| y ./= literal yv

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
-- Current solution is: (3,7)
-- Iteration: 5
-- Current solution is: (4,6)
-- Iteration: 6
-- Current solution is: (5,5)
-- Iteration: 7
-- Current solution is: (6,4)
-- Iteration: 8
-- Current solution is: (7,3)
-- Iteration: 9
-- Current solution is: (8,2)
-- Iteration: 10
-- Current solution is: (9,1)
-- Iteration: 11
-- Current solution is: (10,0)
-- Iteration: 12
-- No other solution!
-- [(0,10),(1,9),(2,8),(3,7),(4,6),(5,5),(6,4),(7,3),(8,2),(9,1),(10,0)]
demo :: IO ()
demo = print =<< runSMT goodSum
