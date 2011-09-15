-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Puzzles.PowerSet
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Computes the powerset of a givenset
-----------------------------------------------------------------------------

module Data.SBV.Examples.Puzzles.PowerSet where

import Data.SBV

genPowerSet :: [SBool] -> SBool
-- The following definition reveals an issue in Yices's model generation. The
-- seemingly vacuous test of checking true-or-false is necessary
-- so that Yices will return a satisfying assignment
-- otherwise, it just skips the "unused" inputs..
genPowerSet = bAll isBool
  where isBool x = x .== true ||| x .== false

powerSet :: [Word8] -> IO ()
powerSet xs = do putStrLn $ "Finding all subsets of " ++ show xs
                 res <- allSat $ mkFreeVars n >>= return . genPowerSet
                 cnt <- displayModels disp res
                 putStrLn $ "Found: " ++ show cnt ++ " subset(s)."
     where n = length xs
           disp i ss
            | length ss /= n = error $ "Expected " ++ show n ++ " results; got: " ++ show (length ss)
            | True           = putStrLn $ "Subset #" ++ show i ++ ": " ++ show (concat (zipWith pick ss xs))
           pick True a  = [a]
           pick False _ = []
