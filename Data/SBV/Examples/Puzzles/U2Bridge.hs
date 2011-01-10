-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Puzzles.U2Bridge
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- The famous U2 bridge crossing puzzle
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE PatternGuards #-}

module Data.SBV.Examples.Puzzles.U2Bridge where

import Data.Maybe(fromJust)
import Control.Monad.State
import Data.SBV
import Data.SBV.Utils.SBVTest

data U2Member = Bono | Edge | Adam | Larry
              deriving (Show, Enum)

type Time      = SWord32
type SU2Member = SWord8

bono, edge, adam, larry :: SU2Member
[bono, edge, adam, larry] = map (fromIntegral . fromEnum) $ [Bono .. Larry]

isU2Member :: SU2Member -> SBool
isU2Member = (.<= larry)  -- 8 bits can represent 256 people; trim it down!

crossTime :: SU2Member -> Time
crossTime = select [  1 {- Bono -}
                   ,  2 {- Edge -}
                   ,  5 {- Adam -}
                   ] 10 {- Larry -}

type Location = SBool
here, there :: Location
[here, there] = [false, bnot here]

data Status = Status { time   :: Time
                     , flash  :: Location
                     , lBono  :: Location
                     , lEdge  :: Location
                     , lAdam  :: Location
                     , lLarry :: Location
                     }

start :: Status
start = Status { time   = 0
               , flash  = here
               , lBono  = here
               , lEdge  = here
               , lAdam  = here
               , lLarry = here
               }

instance Mergeable Status where
  symbolicMerge t s1 s2 = Status { time   = symbolicMerge t (time s1)   (time  s2)
                                 , flash  = symbolicMerge t (flash s1)  (flash s2)
                                 , lBono  = symbolicMerge t (lBono s1)  (lBono s2)
                                 , lEdge  = symbolicMerge t (lEdge s1)  (lEdge s2)
                                 , lAdam  = symbolicMerge t (lAdam s1)  (lAdam s2)
                                 , lLarry = symbolicMerge t (lLarry s1) (lLarry s2)
                                 }

type Move a = State Status a

instance Mergeable a => Mergeable (Move a) where
  symbolicMerge t a b
    = do s <- get
         let (ar, s1) = runState a s
             (br, s2) = runState b s
         put $ symbolicMerge t s1 s2
         return $ symbolicMerge t ar br

peek :: (Status -> a) -> Move a
peek f = do s <- get
            return (f s)

whereIs :: SU2Member -> Move SBool
whereIs p = do [lb, le, la, ll]  <- mapM peek [lBono, lEdge, lAdam, lLarry]
               return $ select [lb, le, la] ll p

xferFlash :: Move ()
xferFlash = modify $ \s -> s{flash = bnot (flash s)}

xferPerson :: SU2Member -> Move ()
xferPerson p =  do [lb, le, la, ll] <- mapM peek [lBono, lEdge, lAdam, lLarry]
                   let lb' = ite (p .== bono)  (bnot lb) lb
                       le' = ite (p .== edge)  (bnot le) le
                       la' = ite (p .== adam)  (bnot la) la
                       ll' = ite (p .== larry) (bnot ll) ll
                   modify $ \s -> s{lBono = lb', lEdge = le', lAdam = la', lLarry = ll'}

bumpTime1 :: SU2Member -> Move ()
bumpTime1 p = modify $ \s -> s{time = time s + crossTime p}

bumpTime2 :: SU2Member -> SU2Member -> Move ()
bumpTime2 p1 p2 = modify $ \s -> s{time = time s + crossTime p1 `smax` crossTime p2}

whenS :: SBool -> Move () -> Move ()
whenS t a = ite t a (return ())

move1 :: SU2Member -> Move ()
move1 p = do f <- peek flash
             l <- whereIs p
             whenS (f .== l) $ do bumpTime1 p
                                  xferFlash
                                  xferPerson p

move2 :: SU2Member -> SU2Member -> Move ()
move2 p1 p2 = do f  <- peek flash
                 l1 <- whereIs p1
                 l2 <- whereIs p2
                 whenS (f .== l1 &&& f .== l2) $ do bumpTime2 p1 p2
                                                    xferFlash
                                                    xferPerson p1
                                                    xferPerson p2

type Actions = [(SBool, SU2Member, SU2Member)]

run :: Actions -> Move [Status]
run = sequence . map step
 where step (b, p1, p2) = ite b (move1 p1) (move2 p1 p2) >> get

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

instance SatModel U2Member where
  parseCWs as = cvtModel cvtCW $ parseCWs as
    where cvtCW :: Word8 -> Maybe U2Member
          cvtCW i = lookup i (zip [0..] [Bono, Edge, Adam, Larry])

solveN :: Int -> IO Bool
solveN n = do putStrLn $ "Checking for solutions with " ++ show n ++ " move" ++ plu n ++ "."
              let genAct = do b  <- free_
                              p1 <- free_
                              p2 <- free_
                              return (b, p1, p2)
              res <- allSat $ mapM (const genAct) [1..n] >>= output . isValid
              cnt <- displayModels disp res
              if cnt == 0 then return False
                          else do putStrLn $ "Found: " ++ show cnt ++ " solution" ++ plu cnt ++ " with " ++ show n ++ " move" ++ plu n ++ "."
                                  return True
  where plu v = if v == 1 then "" else "s"
        disp :: Int -> [(Bool, U2Member, U2Member)] -> IO ()
        disp i ss
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

main :: IO ()
main = go 1
 where go i = do p <- solveN i
                 if p then return () else go (i+1)

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
   "U2Bridge-1" ~: assert $ (0 ==) `fmap` count 1
 , "U2Bridge-2" ~: assert $ (0 ==) `fmap` count 2
 , "U2Bridge-3" ~: assert $ (0 ==) `fmap` count 3
 , "U2Bridge-4" ~: assert $ (0 ==) `fmap` count 4
 , "U2Bridge-5" ~: solve 5 `goldCheck` "U2Bridge.gold"
 , "U2Bridge-6" ~: assert $ (0 ==) `fmap` count 6
 ]
 where act     = do b <- free_; p1 <- free_; p2 <- free_; return (b, p1, p2)
       count n = numberOfModels $ mapM (const act) [1..(n::Int)] >>= output . isValid
       solve n = sat $ mapM (const act) [1..(n::Int)] >>= output . isValid
