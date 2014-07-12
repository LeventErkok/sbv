-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Puzzles.U2Bridge
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- The famous U2 bridge crossing puzzle: <http://www.brainj.net/puzzle.php?id=u2>
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Data.SBV.Examples.Puzzles.U2Bridge where

import Control.Monad       (unless)
import Control.Monad.State (State, runState, put, get, modify, evalState)
import Data.Maybe          (fromJust)

import Data.SBV

-------------------------------------------------------------
-- * Modeling the puzzle
-------------------------------------------------------------

-- | U2 band members
data U2Member = Bono | Edge | Adam | Larry
              deriving (Show, Enum)

-- | Model time using 32 bits
type Time      = SWord32

-- | Each member gets an 8-bit id
type SU2Member = SWord8

-- | Bono's ID
bono :: SU2Member
bono  = fromIntegral . fromEnum $ Bono

-- | Edge's ID
edge :: SU2Member
edge  = fromIntegral . fromEnum $ Edge

-- | Adam's ID
adam :: SU2Member
adam  = fromIntegral . fromEnum $ Adam

-- | Larry's ID
larry :: SU2Member
larry = fromIntegral . fromEnum $ Larry

-- | Is this a valid person?
isU2Member :: SU2Member -> SBool
isU2Member = (.<= larry)  -- 8 bits can represent 256 people; trim it down!

-- | Crossing times for each member of the band
crossTime :: SU2Member -> Time
crossTime = select [  1 {- Bono -}
                   ,  2 {- Edge -}
                   ,  5 {- Adam -}
                   ] 10 {- Larry -}

-- | Location of the flash
type Location = SBool

-- | We represent this side of the bridge as 'here', and arbitrarily as 'false'
here :: Location
here = false

-- | We represent other side of the bridge as 'there', and arbitrarily as 'true'
there :: Location
there = bnot here

-- | The status of the puzzle after each move
data Status = Status { time   :: Time       -- ^ elapsed time
                     , flash  :: Location   -- ^ location of the flash
                     , lBono  :: Location   -- ^ location of Bono
                     , lEdge  :: Location   -- ^ location of Edge
                     , lAdam  :: Location   -- ^ location of Adam
                     , lLarry :: Location   -- ^ location of Larry
                     }

-- | Start configuration, time elapsed is 0 and everybody is 'here'
start :: Status
start = Status { time   = 0
               , flash  = here
               , lBono  = here
               , lEdge  = here
               , lAdam  = here
               , lLarry = here
               }

-- | Mergeable instance for 'Status' simply walks down the structure fields and
-- merges them.
instance Mergeable Status where
  symbolicMerge t s1 s2 = Status { time   = symbolicMerge t (time s1)   (time  s2)
                                 , flash  = symbolicMerge t (flash s1)  (flash s2)
                                 , lBono  = symbolicMerge t (lBono s1)  (lBono s2)
                                 , lEdge  = symbolicMerge t (lEdge s1)  (lEdge s2)
                                 , lAdam  = symbolicMerge t (lAdam s1)  (lAdam s2)
                                 , lLarry = symbolicMerge t (lLarry s1) (lLarry s2)
                                 }

-- | A puzzle move is modeled as a state-transformer
type Move a = State Status a

-- | Mergeable instance for 'Move' simply pushes the merging the data after run of each branch
-- starting from the same state.
instance Mergeable a => Mergeable (Move a) where
  symbolicMerge t a b
    = do s <- get
         let (ar, s1) = runState a s
             (br, s2) = runState b s
         put $ symbolicMerge t s1 s2
         return $ symbolicMerge t ar br

-- | Read the state via an accessor function
peek :: (Status -> a) -> Move a
peek f = do s <- get
            return (f s)

-- | Given an arbitrary member, return his location
whereIs :: SU2Member -> Move SBool
whereIs p = do [lb, le, la, ll]  <- mapM peek [lBono, lEdge, lAdam, lLarry]
               return $ select [lb, le, la] ll p

-- | Transferring the flash to the other side
xferFlash :: Move ()
xferFlash = modify $ \s -> s{flash = bnot (flash s)}

-- | Transferring a person to the other side
xferPerson :: SU2Member -> Move ()
xferPerson p =  do [lb, le, la, ll] <- mapM peek [lBono, lEdge, lAdam, lLarry]
                   let lb' = ite (p .== bono)  (bnot lb) lb
                       le' = ite (p .== edge)  (bnot le) le
                       la' = ite (p .== adam)  (bnot la) la
                       ll' = ite (p .== larry) (bnot ll) ll
                   modify $ \s -> s{lBono = lb', lEdge = le', lAdam = la', lLarry = ll'}

-- | Increment the time, when only one person crosses
bumpTime1 :: SU2Member -> Move ()
bumpTime1 p = modify $ \s -> s{time = time s + crossTime p}

-- | Increment the time, when two people cross together
bumpTime2 :: SU2Member -> SU2Member -> Move ()
bumpTime2 p1 p2 = modify $ \s -> s{time = time s + crossTime p1 `smax` crossTime p2}

-- | Symbolic version of 'when'
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
                 whenS (f .== l1 &&& f .== l2) $ do bumpTime2 p1 p2
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
isValid as = time end .<= 17 &&& bAll check as &&& zigZag there (map flash states) &&& bAll (.== there) [lBono end, lEdge end, lAdam end, lLarry end]
  where check (s, p1, p2) =   isU2Member p1 &&& isU2Member p2
                          -- the following two conditions ensure we find distinct solutions
                          &&& (bnot s ==> p1 .> p2) -- for two person moves, ensure first person is "larger"
                          &&& (s ==> p2 .== bono)   -- for one person moves, ensure second person is always "bono"
        states = evalState (run as) start
        end = last states
        zigZag _ []       = true
        zigZag w (f:rest) = w .== f &&& zigZag (bnot w) rest

-- | The SatModel instance makes it easy to build models, mapping words to U2 members
-- in the way we designated.
instance SatModel U2Member where
  parseCWs as = cvtModel cvtCW $ parseCWs as
    where cvtCW :: Word8 -> Maybe U2Member
          cvtCW i = lookup i (zip [0..] [Bono, Edge, Adam, Larry])

-------------------------------------------------------------
-- * Solving the puzzle
-------------------------------------------------------------

-- | See if there is a solution that has precisely @n@ steps
solveN :: Int -> IO Bool
solveN n = do putStrLn $ "Checking for solutions with " ++ show n ++ " move" ++ plu n ++ "."
              let genAct = do b  <- exists_
                              p1 <- exists_
                              p2 <- exists_
                              return (b, p1, p2)
              res <- allSat $ isValid `fmap` mapM (const genAct) [1..n]
              cnt <- displayModels disp res
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
               go l t ((True, a, _):rest)  = do putStrLn $ sh2 t ++ shL l ++ show a
                                                go (not l) (t + ctime a) rest
               go l t ((False, a, b):rest) = do putStrLn $ sh2 t ++ shL l ++ show a ++ ", " ++ show b
                                                go (not l) (t + ctime a `max` ctime b) rest
               ctime = fromJust . unliteral . crossTime . fromIntegral . fromEnum
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
--  2 <-- Edge
--  4 --> Larry, Adam
-- 14 <-- Bono
-- 15 --> Edge, Bono
-- Total time: 17
-- Solution #2: 
--  0 --> Edge, Bono
--  2 <-- Bono
--  3 --> Larry, Adam
-- 13 <-- Edge
-- 15 --> Edge, Bono
-- Total time: 17
-- Found: 2 solutions with 5 moves.
--
-- Finding all possible solutions to the puzzle.
solveU2 :: IO ()
solveU2 = go 1
 where go i = do p <- solveN i
                 unless p $ go (i+1)
