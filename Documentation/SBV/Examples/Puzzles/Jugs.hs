-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.Jugs
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Solves the classic water jug puzzle: We have 3 jugs. The capacity of the jugs are 8, 5,
-- and 3 gallons. We begin with the 8 gallon jug full, the other two empty. We can transfer
-- from any jug to any other, completely topping off the latter. We want to end with
-- 4 gallons of water in the first and second jugs, and with an empty third jug. What
-- moves should we execute in order to do so?
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Puzzles.Jugs where

import Data.SBV
import Data.SBV.Control

import GHC.Generics(Generic)

-- | A Jug has a capacity (i.e., maximum amount of water it can hold), and content, showing how much
-- it currently has. The invariant is that content is always non-negative and is at most the capacity.
data Jug = Jug { capacity :: Integer
               , content  :: SInteger
               } deriving (Generic, Mergeable)

-- | Transfer from one jug to another. By definition,
-- we transfer to fill the second jug, which may end up
-- filling it fully, or leaving some in the first jug.
transfer :: Jug -> Jug -> (Jug, Jug)
transfer j1 j2 = (j1', j2')
  where empty         = literal (capacity j2) - content j2
        transferrable = empty `smin` content j1
        j1'           = j1 { content = content j1 - transferrable }
        j2'           = j2 { content = content j2 + transferrable }

-- | At the beginning, we have an full 8-gallon jug, and two empty jugs, 5 and 3 gallons each.
initJugs :: (Jug, Jug, Jug)
initJugs = (j1, j2, j3)
  where j1 = Jug 8 8
        j2 = Jug 5 0
        j3 = Jug 3 0

-- | We've solved the puzzle if 8 and 5 gallon jugs have 4 gallons each, and the third one is empty.
solved :: (Jug, Jug, Jug) -> SBool
solved (j1, j2, j3) = content j1 .== 4 .&& content j2 .== 4 .&& content j3 .== 0

-- | Execute a bunch of moves.
moves :: [(SInteger, SInteger)] -> (Jug, Jug, Jug)
moves = foldl move initJugs
  where move :: (Jug, Jug, Jug) -> (SInteger, SInteger) -> (Jug, Jug, Jug)
        move (j0, j1, j2) (from, to) =
              ite ((from, to) .== (1, 2)) (let (j0', j1') = transfer j0 j1 in (j0', j1', j2))
            $ ite ((from, to) .== (2, 1)) (let (j1', j0') = transfer j1 j0 in (j0', j1', j2))
            $ ite ((from, to) .== (1, 3)) (let (j0', j2') = transfer j0 j2 in (j0', j1,  j2'))
            $ ite ((from, to) .== (3, 1)) (let (j2', j0') = transfer j2 j0 in (j0', j1,  j2'))
            $ ite ((from, to) .== (2, 3)) (let (j1', j2') = transfer j1 j2 in (j0,  j1', j2'))
            $ ite ((from, to) .== (3, 2)) (let (j2', j1') = transfer j2 j1 in (j0,  j1', j2'))
                                          (j0, j1, j2)

-- | Solve the puzzle. We have:
--
-- >>> puzzle
-- # of moves: 0
-- # of moves: 1
-- # of moves: 2
-- # of moves: 3
-- # of moves: 4
-- # of moves: 5
-- # of moves: 6
-- # of moves: 7
-- 1 --> 2
-- 2 --> 3
-- 3 --> 1
-- 2 --> 3
-- 1 --> 2
-- 2 --> 3
-- 3 --> 1
--
-- Here's the contents in terms of gallons after each move:
-- (8, 0, 0)
-- (3, 5, 0)
-- (3, 2, 3)
-- (6, 2, 0)
-- (6, 0, 2)
-- (1, 5, 2)
-- (1, 4, 3)
-- (4, 4, 0)
--
-- Note that by construction this is the minimum length solution. (Though our construction
-- does not guarantee that it is unique.)
puzzle :: IO ()
puzzle = runSMT $ do
            let run i = do io $ putStrLn $ "# of moves: " ++ show (i :: Int)
                           push 1
                           ms <- mapM (const genMove) [1..i]
                           constrain $ solved $ moves ms
                           cs <- checkSat
                           case cs of
                             Unsat -> do pop 1
                                         run (i+1)
                             Sat   -> mapM_ sh ms
                             _     -> error $ "Unexpected result: " ++ show cs
            query $ run 0
  where genMove = (,) <$> freshVar_ <*> freshVar_
        sh (f, t) = do from <- getValue f
                       to   <- getValue t
                       io $ putStrLn $ show from ++ " --> " ++ show to
