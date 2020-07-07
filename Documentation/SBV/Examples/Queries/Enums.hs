-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Queries.Enums
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrates the use of enumeration values during queries.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Queries.Enums where

import Data.SBV
import Data.SBV.Control

-- | Days of the week. We make it symbolic using the 'mkSymbolicEnumeration' splice.
data Day = Monday | Tuesday | Wednesday | Thursday | Friday | Saturday | Sunday

-- | Make 'Day' a symbolic value.
mkSymbolicEnumeration ''Day

-- | A trivial query to find three consecutive days that's all before 'Thursday'. The point
-- here is that we can perform queries on such enumerated values and use 'getValue' on them
-- and return their values from queries just like any other value. We have:
--
-- >>> findDays
-- [Monday,Tuesday,Wednesday]
findDays :: IO [Day]
findDays = runSMT $ do (d1 :: SDay) <- free "d1"
                       (d2 :: SDay) <- free "d2"
                       (d3 :: SDay) <- free "d3"

                       -- Assert that they are ordered
                       constrain $ d1 .<= d2
                       constrain $ d2 .<= d3

                       -- Assert that last day is before 'Thursday'
                       constrain $ d3 .< sThursday

                       -- Constraints can be given before or after
                       -- the query mode starts. We will assert that
                       -- they are different after we start interacting
                       -- with the solver. Note that we can query the
                       -- values based on other values obtained too,
                       -- if we want to guide the search.

                       query $ do constrain $ distinct [d1, d2, d3]

                                  cs <- checkSat
                                  case cs of
                                    Sat -> do a <- getValue d1
                                              b <- getValue d2
                                              c <- getValue d3
                                              return [a, b, c]

                                    _   -> error "Impossible, can't find days!"
