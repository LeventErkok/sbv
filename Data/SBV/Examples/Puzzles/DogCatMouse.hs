{- (c) Copyright Levent Erkok. All rights reserved.
--
-- The sbv library is distributed with the BSD3 license. See the LICENSE file
-- in the distribution for details.
-}

module Data.SBV.Examples.Puzzles.DogCatMouse where

import Data.SBV

{- Puzzle:
     Spend exactly 100 dollars and buy exactly 100 animals.
     Dogs cost 15 dollars, cats cost 1 dollar, and mice cost 25 cents each.
     You have to buy at least one of each.
     How many should you buy?
-}

type Count = SWord16 -- much larger than we actually need, but it works..

puzzle :: Count -> Count -> Count -> SBool
puzzle dog cat mouse =
         dog   .>= 1 &&& dog   .<= 98                  -- at least one dog and at most 98
    &&&  cat   .>= 1 &&& cat   .<= 98                  -- ditto for cats
    &&&  mouse .>= 1 &&& mouse .<= 98                  -- ditto for mice
    &&&  dog + cat + mouse .== 100                     -- buy precisely 100 animals
    &&&  1500 * dog + 100 * cat + 25 * mouse .== 10000 -- spend exactly 100 dollars (use cents since we don't have fractions)

-- returns the only solution:
--   dog = 3 :: [16U]
--   cat = 41 :: [16U]
--   mouse = 56 :: [16U
main :: IO ()
main = print =<< allSat (forAll ["dog", "cat", "mouse"] puzzle)

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
  "dog cat mouse" ~: allSat puzzle `goldCheck` "dogCatMouse.gold"
 ]
