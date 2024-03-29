-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.Euler185
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A solution to Project Euler problem #185: <http://projecteuler.net/index.php?section=problems&id=185>
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Puzzles.Euler185 where

import Data.Char (ord)
import Data.SBV

-- | The given guesses and the correct digit counts, encoded as a simple list.
guesses :: [(String, SWord8)]
guesses = [ ("5616185650518293", 2), ("3847439647293047", 1), ("5855462940810587", 3)
          , ("9742855507068353", 3), ("4296849643607543", 3), ("3174248439465858", 1)
          , ("4513559094146117", 2), ("7890971548908067", 3), ("8157356344118483", 1)
          , ("2615250744386899", 2), ("8690095851526254", 3), ("6375711915077050", 1)
          , ("6913859173121360", 1), ("6442889055042768", 2), ("2321386104303845", 0)
          , ("2326509471271448", 2), ("5251583379644322", 2), ("1748270476758276", 3)
          , ("4895722652190306", 1), ("3041631117224635", 3), ("1841236454324589", 3)
          , ("2659862637316867", 2)
          ]

-- | Encode the problem, note that we check digits are within 0-9 as
-- we use 8-bit words to represent them. Otherwise, the constraints are simply
-- generated by zipping the alleged solution with each guess, and making sure the
-- number of matching digits match what's given in the problem statement.
euler185 :: Symbolic SBool
euler185 = do soln <- mkFreeVars 16
              return $ sAll digit soln .&& sAnd (map (genConstr soln) guesses)
  where genConstr a (b, c) = sum (zipWith eq a b) .== (c :: SWord8)
        digit x = (x :: SWord8) .>= 0 .&& x .<= 9
        eq x y =  ite (x .== fromIntegral (ord y - ord '0')) 1 0

-- | Print out the solution nicely. We have:
--
-- >>> solveEuler185
-- 4640261571849533
-- Number of solutions: 1
solveEuler185 :: IO ()
solveEuler185 = do res <- allSat euler185
                   cnt <- displayModels id disp res
                   putStrLn $ "Number of solutions: " ++ show cnt
   where disp _ (_, ss) = putStrLn $ concatMap show (ss :: [Word8])
