-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Puzzles.Temperature
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Puzzle:
--   What 2 digit fahrenheit/celcius values are reverses of each other?
--   Ignoring the fractions in the conversion
-----------------------------------------------------------------------------

module Data.SBV.Examples.Puzzles.Temperature where

import Data.SBV

type Temp = SWord16 -- larger than we need actually

-- convert celcius to fahrenheit, rounding up/down properly
-- we have to be careful here to make sure rounding is done properly..
d2f :: Temp -> Temp
d2f d = 32 + ite (fr .>= 5) (1+fi) fi
  where (fi, fr) = (18 * d) `bvQuotRem` 10

-- puzzle: What 2 digit fahrenheit/celcius values are reverses of each other?
revOf :: Temp -> SBool
revOf c = swap (digits c) .== digits (d2f c)
  where digits x = x `bvQuotRem` 10
        swap (a, b) = (b, a)

solve :: IO ()
solve = do res <- allSat $ revOf `fmap` exists_
           cnt <- displayModels disp res
           putStrLn $ "Found " ++ show cnt ++ " solutions."
     where disp :: Int -> Word16 -> IO ()
           disp _ x = putStrLn $ " " ++ show x ++ "C --> " ++ show (round f :: Integer) ++ "F (exact value: " ++ show f ++ "F)"
              where f :: Double
                    f  = 32 + (9 * fromIntegral x) / 5
