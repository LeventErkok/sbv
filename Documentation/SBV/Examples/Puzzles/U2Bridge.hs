-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.U2Bridge
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- The famous U2 bridge crossing puzzle: <http://www.braingle.com/brainteasers/515/u2.html>
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-incomplete-uni-patterns #-}

module Documentation.SBV.Examples.Puzzles.U2Bridge where

import Control.Monad       (unless)
import Control.Monad.State (State, runState, put, get, gets, modify, evalState)

import Data.List(sortOn)

import GHC.Generics (Generic)

import Data.SBV

-------------------------------------------------------------
-- * Modeling the puzzle
-------------------------------------------------------------

-- | U2 band members. We want to translate this to SMT-Lib as a data-type, and hence the
-- call to mkSymbolicEnumeration.
data U2Member = Bono | Edge | Adam | Larry

-- | Make 'U2Member' a symbolic value.
mkSymbolicEnumeration ''U2Member

-- | Model time using 32 bits
type Time  = Word32

-- | Symbolic variant for time
type STime = SBV Time

-- | Crossing times for each member of the band
crossTime :: U2Member -> Time
crossTime Bono  = 1
crossTime Edge  = 2
crossTime Adam  = 5
crossTime Larry = 10

-- | The symbolic variant.. The duplication is unfortunate.
sCrossTime :: SU2Member -> STime
sCrossTime m =   ite (m .== sBono) (literal (crossTime Bono))
               $ ite (m .== sEdge) (literal (crossTime Edge))
               $ ite (m .== sAdam) (literal (crossTime Adam))
                                   (literal (crossTime Larry)) -- Must be Larry

-- | Location of the flash
data Location = Here | There

-- | Make 'Location' a symbolic value.
mkSymbolicEnumeration ''Location

-- | The status of the puzzle after each move
--
-- This type is equipped with an automatically derived 'Mergeable' instance
-- because each field is 'Mergeable'. A 'Generic' instance must also be derived
-- for this to work, and the @DeriveAnyClass@ language extension must be
-- enabled. The derived 'Mergeable' instance simply walks down the structure
-- field by field and merges each one. An equivalent hand-written 'Mergeable'
-- instance is provided in a comment below.
data Status = Status { time   :: STime       -- ^ elapsed time
                     , flash  :: SLocation   -- ^ location of the flash
                     , lBono  :: SLocation   -- ^ location of Bono
                     , lEdge  :: SLocation   -- ^ location of Edge
                     , lAdam  :: SLocation   -- ^ location of Adam
                     , lLarry :: SLocation   -- ^ location of Larry
                     } deriving (Generic, Mergeable)

-- The derived Mergeable instance is equivalent to the following:
--
-- instance Mergeable Status where
--   symbolicMerge f t s1 s2 = Status { time   = symbolicMerge f t (time   s1) (time   s2)
--                                    , flash  = symbolicMerge f t (flash  s1) (flash  s2)
--                                    , lBono  = symbolicMerge f t (lBono  s1) (lBono  s2)
--                                    , lEdge  = symbolicMerge f t (lEdge  s1) (lEdge  s2)
--                                    , lAdam  = symbolicMerge f t (lAdam  s1) (lAdam  s2)
--                                    , lLarry = symbolicMerge f t (lLarry s1) (lLarry s2)
--                                    }

-- | Start configuration, time elapsed is 0 and everybody is here
start :: Status
start = Status { time   = 0
               , flash  = sHere
               , lBono  = sHere
               , lEdge  = sHere
               , lAdam  = sHere
               , lLarry = sHere
               }

-- | A puzzle move is modeled as a state-transformer
type Move a = State Status a

-- | Mergeable instance for 'Move' simply pushes the merging the data after run of each branch
-- starting from the same state.
instance Mergeable a => Mergeable (Move a) where
  symbolicMerge f t a b
    = do s <- get
         let (ar, s1) = runState a s
             (br, s2) = runState b s
         put $ symbolicMerge f t s1 s2
         return $ symbolicMerge f t ar br

-- | Read the state via an accessor function
peek :: (Status -> a) -> Move a
peek = gets

-- | Given an arbitrary member, return his location
whereIs :: SU2Member -> Move SLocation
whereIs p =  ite (p .== sBono) (peek lBono)
           $ ite (p .== sEdge) (peek lEdge)
           $ ite (p .== sAdam) (peek lAdam)
                               (peek lLarry)

-- | Transferring the flash to the other side
xferFlash :: Move ()
xferFlash = modify $ \s -> s{flash = ite (flash s .== sHere) sThere sHere}

-- | Transferring a person to the other side
xferPerson :: SU2Member -> Move ()
xferPerson p =  do ~[lb, le, la, ll] <- mapM peek [lBono, lEdge, lAdam, lLarry]
                   let move l = ite (l .== sHere) sThere sHere
                       lb' = ite (p .== sBono)  (move lb) lb
                       le' = ite (p .== sEdge)  (move le) le
                       la' = ite (p .== sAdam)  (move la) la
                       ll' = ite (p .== sLarry) (move ll) ll
                   modify $ \s -> s{lBono = lb', lEdge = le', lAdam = la', lLarry = ll'}

-- | Increment the time, when only one person crosses
bumpTime1 :: SU2Member -> Move ()
bumpTime1 p = modify $ \s -> s{time = time s + sCrossTime p}

-- | Increment the time, when two people cross together
bumpTime2 :: SU2Member -> SU2Member -> Move ()
bumpTime2 p1 p2 = modify $ \s -> s{time = time s + sCrossTime p1 `smax` sCrossTime p2}

-- | Symbolic version of 'Control.Monad.when'
whenS :: SBool -> Move () -> Move ()
whenS t a = ite t a (return ())

-- | Move one member, remembering to take the flash
move1 :: SU2Member -> Move ()
move1 p = do f <- peek flash
             l <- whereIs p
             -- only do the move if the person and the flash are at the same side
             whenS (f .== l) $ do bumpTime1 p
                                  xferFlash
                                  xferPerson p

-- | Move two members, again with the flash
move2 :: SU2Member -> SU2Member -> Move ()
move2 p1 p2 = do f  <- peek flash
                 l1 <- whereIs p1
                 l2 <- whereIs p2
                 -- only do the move if both people and the flash are at the same side
                 whenS (f .== l1 .&& f .== l2) $ do bumpTime2 p1 p2
                                                    xferFlash
                                                    xferPerson p1
                                                    xferPerson p2

-------------------------------------------------------------
-- * Actions
-------------------------------------------------------------

-- | A move action is a sequence of triples. The first component is symbolically
-- True if only one member crosses. (In this case the third element of the triple
-- is irrelevant.) If the first component is (symbolically) False, then both members
-- move together
type Actions = [(SBool, SU2Member, SU2Member)]

-- | Run a sequence of given actions.
run :: Actions -> Move [Status]
run = mapM step
 where step (b, p1, p2) = ite b (move1 p1) (move2 p1 p2) >> get

-------------------------------------------------------------
-- * Recognizing valid solutions
-------------------------------------------------------------

-- | Check if a given sequence of actions is valid, i.e., they must all
-- cross the bridge according to the rules and in less than 17 seconds
isValid :: Actions -> SBool
isValid as = time end .<= 17 .&& sAll check as .&& zigZag (cycle [sThere, sHere]) (map flash states) .&& sAll (.== sThere) [lBono end, lEdge end, lAdam end, lLarry end]
  where check (s, p1, p2) =   (sNot s .=> p1 .> p2)       -- for two person moves, ensure first person is "larger"
                          .&& (s      .=> p2 .== sBono)   -- for one person moves, ensure second person is always "bono"
        states = evalState (run as) start
        end = last states
        zigZag reqs locs = sAnd $ zipWith (.==) locs reqs

-------------------------------------------------------------
-- * Solving the puzzle
-------------------------------------------------------------

-- | See if there is a solution that has precisely @n@ steps
solveN :: Int -> IO Bool
solveN n = do putStrLn $ "Checking for solutions with " ++ show n ++ " move" ++ plu n ++ "."
              let genAct = do b  <- free_
                              p1 <- free_
                              p2 <- free_
                              return (b, p1, p2)
              res <- allSat $ isValid `fmap` mapM (const genAct) [1..n]
              cnt <- displayModels (sortOn show) disp res
              if cnt == 0 then return False
                          else do putStrLn $ "Found: " ++ show cnt ++ " solution" ++ plu cnt ++ " with " ++ show n ++ " move" ++ plu n ++ "."
                                  return True
  where plu v = if v == 1 then "" else "s"
        disp :: Int -> (Bool, [(Bool, U2Member, U2Member)]) -> IO ()
        disp i (_, ss)
         | lss /= n = error $ "Expected " ++ show n ++ " results; got: " ++ show lss
         | True     = do putStrLn $ "Solution #" ++ show i ++ ": "
                         go False 0 ss
                         return ()
         where lss  = length ss
               go _ t []                   = putStrLn $ "Total time: " ++ show t
               go l t ((True,  a, _):rest) = do putStrLn $ sh2 t ++ shL l ++ show a
                                                go (not l) (t + crossTime a) rest
               go l t ((False, a, b):rest) = do putStrLn $ sh2 t ++ shL l ++ show a ++ ", " ++ show b
                                                go (not l) (t + crossTime a `max` crossTime b) rest
               sh2 t = let s = show t in if length s < 2 then ' ' : s else s
               shL False = " --> "
               shL True  = " <-- "

-- | Solve the U2-bridge crossing puzzle, starting by testing solutions with
-- increasing number of steps, until we find one. We have:
--
-- >>> solveU2
-- Checking for solutions with 1 move.
-- Checking for solutions with 2 moves.
-- Checking for solutions with 3 moves.
-- Checking for solutions with 4 moves.
-- Checking for solutions with 5 moves.
-- Solution #1:
--  0 --> Edge, Bono
--  2 <-- Bono
--  3 --> Larry, Adam
-- 13 <-- Edge
-- 15 --> Edge, Bono
-- Total time: 17
-- Solution #2:
--  0 --> Edge, Bono
--  2 <-- Edge
--  4 --> Larry, Adam
-- 14 <-- Bono
-- 15 --> Edge, Bono
-- Total time: 17
-- Found: 2 solutions with 5 moves.
--
-- Finding all possible solutions to the puzzle.
solveU2 :: IO ()
solveU2 = go 1
 where go i = do p <- solveN i
                 unless p $ go (i+1)
