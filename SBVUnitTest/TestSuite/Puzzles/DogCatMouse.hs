-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Puzzles.DogCatMouse
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Data.SBV.Examples.Puzzles.DogCatMouse
-----------------------------------------------------------------------------

module TestSuite.Puzzles.DogCatMouse(tests) where

import Data.SBV
-- import Data.SBV.Examples.Puzzles.DogCatMouse   -- everything defined here

import SBVTest

-- Test suite
tests :: TestTree
tests =
  testGroup "Puzzles.DogCatMouse"
    [ goldenVsStringShow "dog_cat_mouse" "dogCatMouse.gold" (allSat p)
    ]
 where p = do [dog, cat, mouse] <- sIntegers ["dog", "cat", "mouse"]
              solve [ dog   .>= 1                                   -- at least one dog
                    , cat   .>= 1                                   -- at least one cat
                    , mouse .>= 1                                   -- at least one mouse
                    , dog + cat + mouse .== 100                     -- buy precisely 100 animals
                    , 1500 * dog + 100 * cat + 25 * mouse .== 10000 -- spend exactly 100 dollars (use cents since we don't have fractions)
                    ]
