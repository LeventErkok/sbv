-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.Fish
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Solves the following logic puzzle, attributed to Albert Einstein:
--
--   - The Briton lives in the red house.
--   - The Swede keeps dogs as pets.
--   - The Dane drinks tea.
--   - The green house is left to the white house.
--   - The owner of the green house drinks coffee.
--   - The person who plays football rears birds.
--   - The owner of the yellow house plays baseball.
--   - The man living in the center house drinks milk.
--   - The Norwegian lives in the first house.
--   - The man who plays volleyball lives next to the one who keeps cats.
--   - The man who keeps the horse lives next to the one who plays baseball.
--   - The owner who plays tennis drinks beer.
--   - The German plays hockey.
--   - The Norwegian lives next to the blue house.
--   - The man who plays volleyball has a neighbor who drinks water.
--
-- Who owns the fish?
------------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}

module Documentation.SBV.Examples.Puzzles.Fish where

import Data.SBV

-- | Colors of houses
data Color = Red | Green | White | Yellow | Blue

-- | Make 'Color' a symbolic value.
mkSymbolicEnumeration ''Color

-- | Nationalities of the occupants
data Nationality = Briton | Dane | Swede | Norwegian | German

-- | Make 'Nationality' a symbolic value.
mkSymbolicEnumeration ''Nationality

-- | Beverage choices
data Beverage = Tea | Coffee | Milk | Beer | Water

-- | Make 'Beverage' a symbolic value.
mkSymbolicEnumeration ''Beverage

-- | Pets they keep
data Pet = Dog | Horse | Cat | Bird | Fish

-- | Make 'Pet' a symbolic value.
mkSymbolicEnumeration ''Pet

-- | Sports they engage in
data Sport = Football | Baseball | Volleyball | Hockey | Tennis

-- | Make 'Sport' a symbolic value.
mkSymbolicEnumeration ''Sport

-- | We have:
--
-- >>> fishOwner
-- German
--
-- It's not hard to modify this program to grab the values of all the assignments, i.e., the full
-- solution to the puzzle. We leave that as an exercise to the interested reader!
-- NB. We use the 'allSatTrackUFs' configuration to indicate that the uninterpreted function
-- changes do not matter for generating different values. All we care is that the fishOwner changes!
fishOwner :: IO ()
fishOwner = do vs <- getModelValues "fishOwner" `fmap` allSatWith z3{allSatTrackUFs = False} puzzle
               case vs of
                 [Just (v::Nationality)] -> print v
                 []                      -> error "no solution"
                 _                       -> error "no unique solution"
 where puzzle = do

          let c = uninterpret "color"
              n = uninterpret "nationality"
              b = uninterpret "beverage"
              p = uninterpret "pet"
              s = uninterpret "sport"

          let i `neighbor` j = i .== j+1 .|| j .== i+1
              a `is`       v = a .== literal v

          let fact0   = constrain
              fact1 f = do i <- free_
                           constrain $ 1 .<= i .&& i .<= (5 :: SInteger)
                           constrain $ f i
              fact2 f = do i <- free_
                           j <- free_
                           constrain $ 1 .<= i .&& i .<= (5 :: SInteger)
                           constrain $ 1 .<= j .&& j .<= 5
                           constrain $ i ./= j
                           constrain $ f i j

          fact1 $ \i   -> n i `is` Briton     .&& c i `is` Red
          fact1 $ \i   -> n i `is` Swede      .&& p i `is` Dog
          fact1 $ \i   -> n i `is` Dane       .&& b i `is` Tea
          fact2 $ \i j -> c i `is` Green      .&& c j `is` White    .&& i .== j-1
          fact1 $ \i   -> c i `is` Green      .&& b i `is` Coffee
          fact1 $ \i   -> s i `is` Football   .&& p i `is` Bird
          fact1 $ \i   -> c i `is` Yellow     .&& s i `is` Baseball
          fact0 $         b 3 `is` Milk
          fact0 $         n 1 `is` Norwegian
          fact2 $ \i j -> s i `is` Volleyball .&& p j `is` Cat      .&& i `neighbor` j
          fact2 $ \i j -> p i `is` Horse      .&& s j `is` Baseball .&& i `neighbor` j
          fact1 $ \i   -> s i `is` Tennis     .&& b i `is` Beer
          fact1 $ \i   -> n i `is` German     .&& s i `is` Hockey
          fact2 $ \i j -> n i `is` Norwegian  .&& c j `is` Blue     .&& i `neighbor` j
          fact2 $ \i j -> s i `is` Volleyball .&& b j `is` Water    .&& i `neighbor` j

          ownsFish <- free "fishOwner"
          fact1 $ \i -> n i .== ownsFish .&& p i `is` Fish
