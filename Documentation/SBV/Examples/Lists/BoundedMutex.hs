-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Lists.BoundedMutex
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proves a simple mutex algorithm correct up to a given bound.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Lists.BoundedMutex where

import Data.SBV
import Data.SBV.Control

-- | Each agent can be in one of the three states
data State = Idle     -- ^ Regular work
           | Ready    -- ^ Intention to enter critical state
           | Critical -- ^ In the critical state
           deriving (Show, Enum, Bounded)

-- | Make 'State' a symbolic enumeration
mkSymbolic [''State]

-- | The mutex property holds for two sequences of state transitions, if they are not in
-- their critical section at the same time.
mutex :: [SState] -> [SState] -> SBool
mutex p1s p2s = sAnd $ zipWith (\p1 p2 -> p1 ./= sCritical .|| p2 ./= sCritical) p1s p2s

-- | A sequence is valid upto a bound if it starts at 'Idle', and follows the mutex rules. That is:
--
--    * From 'Idle' it can switch to 'Ready' or stay 'Idle'
--    * From 'Ready' it can switch to 'Critical' if it's its turn
--    * From 'Critical' it can either stay in 'Critical' or go back to 'Idle'
--
-- The variable @me@ identifies the agent id.
validSequence :: Integer -> [SInteger] -> [SState] -> SBool
validSequence _  []     _           = sTrue
validSequence _  _      []          = sTrue
validSequence me pturns procs@(p:_) = sAnd [ sIdle .== p
                                           , check pturns procs sIdle
                                           ]
   where check []           _          _    = sTrue
         check _            []         _    = sTrue
         check (turn:turns) (cur:rest) prev = ok .&& check turns rest cur
           where ok = ite (prev .== sIdle)                          (cur `sElem` [sIdle, sReady])
                    $ ite (prev .== sReady .&& turn .== literal me) (cur `sElem` [sCritical])
                    $ ite (prev .== sCritical)                      (cur `sElem` [sCritical, sIdle])
                                                                    (cur `sElem` [prev])

-- | The mutex algorithm, coded implicitly as an assignment to turns. Turns start at @1@, and at each stage is either
-- @1@ or @2@; giving preference to that process. The only condition is that if either process is in its critical
-- section, then the turn value stays the same. Note that this is sufficient to satisfy safety (i.e., mutual
-- exclusion), though it does not guarantee liveness.
validTurns :: [SInteger] -> [SState] -> [SState] -> SBool
validTurns []                    _        _        = sTrue
validTurns turns@(firstTurn : _) process1 process2 = firstTurn .== 1 .&& check (zip3 turns process1 process2) 1
  where check []                     _    = sTrue
        check ((cur, p1, p2) : rest) prev =   cur `sElem` map literal [1, 2]
                                          .&& (p1 .== sCritical .|| p2 .== sCritical .=> cur .== prev)
                                          .&& check rest cur

-- | Check that we have the mutex property so long as 'validSequence' and 'validTurns' holds; i.e.,
-- so long as both the agents and the arbiter act according to the rules. The check is bounded up-to-the
-- given concrete bound; so this is an example of a bounded-model-checking style proof. We have:
--
-- >>> checkMutex 20
-- All is good!
checkMutex :: Int -> IO ()
checkMutex b = runSMT $ do
                  p1    :: [SState]   <- mapM (\i -> free ("p1_" ++ show i)) [1 .. b]
                  p2    :: [SState]   <- mapM (\i -> free ("p2_" ++ show i)) [1 .. b]
                  turns :: [SInteger] <- mapM (\i -> free ("t_"  ++ show i)) [1 .. b]

                  -- Ensure that both sequences and the turns are valid
                  constrain $ validSequence 1 turns p1
                  constrain $ validSequence 2 turns p2
                  constrain $ validTurns      turns p1 p2

                  -- Try to assert that mutex does not hold. If we get a
                  -- counter example, we would've found a violation!
                  constrain $ sNot $ mutex p1 p2

                  query $ do cs <- checkSat
                             case cs of
                               Unk    -> error "Solver said Unknown!"
                               DSat{} -> error "Solver said delta-satisfiable!"
                               Unsat  -> io . putStrLn $ "All is good!"
                               Sat    -> do io . putStrLn $ "Violation detected!"
                                            do p1V <- mapM getValue p1
                                               p2V <- mapM getValue p2
                                               ts  <- mapM getValue turns

                                               io . putStrLn $ "P1: " ++ show p1V
                                               io . putStrLn $ "P2: " ++ show p2V
                                               io . putStrLn $ "Ts: " ++ show ts

-- | Our algorithm is correct, but it is not fair. It does not guarantee that a process that
-- wants to enter its critical-section will always do so eventually. Demonstrate this by
-- trying to show a bounded trace of length 10, such that the second process is ready but
-- never transitions to critical. We have:
--
-- >>> notFair 10
-- Fairness is violated at bound: 10
-- P1: [Idle,Idle,Ready,Critical,Idle,Ready,Critical,Critical,Idle,Ready]
-- P2: [Idle,Ready,Ready,Ready,Ready,Ready,Ready,Ready,Ready,Ready]
-- Ts: [1,1,1,1,1,1,1,1,1,1]
--
-- As expected, P2 gets ready but never goes critical since the arbiter keeps picking
-- P1 unfairly. (You might get a different trace depending on what z3 happens to produce!)
--
-- Exercise for the reader: Change the 'validTurns' function so that it alternates the turns
-- from the previous value if neither process is in critical. Show that this makes the 'notFair'
-- function below no longer exhibits the issue. Is this sufficient? Concurrent programming is tricky!
notFair :: Int -> IO ()
notFair b = runSMT $ do p1    :: [SState]   <- mapM (\i -> free ("p1_" ++ show i)) [1 .. b]
                        p2    :: [SState]   <- mapM (\i -> free ("p2_" ++ show i)) [1 .. b]
                        turns :: [SInteger] <- mapM (\i -> free ("t_"  ++ show i)) [1 .. b]

                        -- Ensure that both sequences and the turns are valid
                        constrain $ validSequence 1 turns p1
                        constrain $ validSequence 2 turns p2
                        constrain $ validTurns    turns p1 p2

                        -- Ensure that the second process becomes ready in the second cycle:
                        constrain $ p2 !! 1 .== sReady

                        -- Find a trace where p2 never goes critical
                        -- counter example, we would've found a violation!
                        constrain $ sNot $ sCritical `sElem` p2

                        query $ do cs <- checkSat
                                   case cs of
                                     Unk    -> error "Solver said Unknown!"
                                     DSat{} -> error "Solver said delta-satisfiable!"
                                     Unsat  -> error "Solver couldn't find a violating trace!"
                                     Sat    -> do io . putStrLn $ "Fairness is violated at bound: " ++ show b
                                                  do p1V <- mapM getValue p1
                                                     p2V <- mapM getValue p2
                                                     ts  <- mapM getValue turns

                                                     io . putStrLn $ "P1: " ++ show p1V
                                                     io . putStrLn $ "P2: " ++ show p2V
                                                     io . putStrLn $ "Ts: " ++ show ts

{- HLint ignore module "Reduce duplication" -}
