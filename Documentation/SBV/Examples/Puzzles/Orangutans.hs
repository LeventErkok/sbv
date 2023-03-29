-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.Orangutans
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Based on <http://github.com/goldfirere/video-resources/blob/main/2022-08-12-java/Haskell.hs>
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE OverloadedRecordDot #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Puzzles.Orangutans where

import Data.SBV
import GHC.Generics (Generic)

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV

-- | Orangutans in the puzzle.
data Orangutan = Merah   | Ofallo  | Quirrel  | Shamir   deriving (Enum, Bounded)

-- | Handlers for each orangutan.
data Handler   = Dolly   | Eva     | Francine | Gracie

-- | Location for each orangutan.
data Location  = Ambalat | Basahan | Kendisi  | Tarakan

mkSymbolicEnumeration ''Orangutan
mkSymbolicEnumeration ''Handler
mkSymbolicEnumeration ''Location

-- | An assignment is solution to the puzzle
data Assignment = MkAssignment { orangutan :: SOrangutan
                               , handler   :: SHandler
                               , location  :: SLocation
                               , age       :: SInteger
                               }
                               deriving (Generic, Mergeable)

-- | Create a symbolic assignment, using symbolic fields.
mkSym :: Orangutan -> Symbolic Assignment
mkSym o = do let h = show o ++ ".handler"
                 l = show o ++ ".location"
                 a = show o ++ ".age"
             s <- MkAssignment (literal o) <$> free h <*> free l <*> free a
             constrain $ s.age `sElem` [4, 7, 10, 13]
             pure s

-- | We get:
--
-- >>> allSat puzzle
-- Solution #1:
--   Merah.handler    =   Gracie :: Handler
--   Merah.location   =  Tarakan :: Location
--   Merah.age        =       10 :: Integer
--   Ofallo.handler   =      Eva :: Handler
--   Ofallo.location  =  Kendisi :: Location
--   Ofallo.age       =       13 :: Integer
--   Quirrel.handler  =    Dolly :: Handler
--   Quirrel.location =  Basahan :: Location
--   Quirrel.age      =        4 :: Integer
--   Shamir.handler   = Francine :: Handler
--   Shamir.location  =  Ambalat :: Location
--   Shamir.age       =        7 :: Integer
-- This is the only solution.
puzzle :: ConstraintSet
puzzle = do
   solution@[_merah, ofallo, quirrel, shamir] <- mapM mkSym [minBound .. maxBound]

   let find f = foldr1 (\a1 a2 -> ite (f a1) a1 a2) solution

   -- 0. All are different in terms of handlers, locations, and ages
   constrain $ distinct (map (.handler)  solution)
   constrain $ distinct (map (.location) solution)
   constrain $ distinct (map (.age)      solution)

   -- 1. Shamir is 7 years old.
   constrain $ shamir.age .== 7

   -- 2. Shamir came from Ambalat.
   constrain $ shamir.location .== sAmbalat

   -- 3. Quirrel is younger than the ape that was found in Tarakan.
   let tarakan = find (\a -> a.location .== sTarakan)
   constrain $ quirrel.age .< tarakan.age

   -- 4. Of Ofallo and the ape that was found in Tarakan, one is cared for by Gracie and the other is 13 years old.
   let clue4 a1 a2 = a1.handler .== sGracie .&& a2.age .== 13
   constrain $ clue4 ofallo tarakan .|| clue4 tarakan ofallo
   constrain $ sOfallo ./= tarakan.orangutan

   -- 5. The animal that was found in Ambalat is either the 10-year-old or the animal Francine works with.
   let ambalat = find (\a -> a.location .== sAmbalat)
   constrain $ ambalat.age .== 10 .|| ambalat.handler .== sFrancine

   -- 6. Ofallo isn't 10 years old.
   constrain $ ofallo.age ./= 10

   -- 7. The ape that was found in Kendisi is older than the ape Dolly works with.
   let kendisi = find (\a -> a.location .== sKendisi)
   let dolly   = find (\a -> a.handler  .== sDolly)
   constrain $ kendisi.age .> dolly.age
