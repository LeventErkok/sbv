-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Queries.Enums
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Demonstrates the use of enumeration values during queries.
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveAnyClass     #-}

module Data.SBV.Examples.Queries.Enums where

import Data.SBV
import Data.SBV.Control
import Data.Generics

-- | Days of the week. The bulky @deriving@ clause is necessary to make this
-- type usable as a symbolic kind in SBV.
data Day = Monday | Tuesday | Wednesday | Thursday | Friday | Saturday | Sunday
         deriving (Eq, Ord, Show, Read, Data, SymWord, HasKind, SMTValue)

-- | The type synonym 'SDay' is the symbolic variant of 'Day'. (Similar to 'SInteger'/'Integer'
-- and others.)
type SDay = SBV Day

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
                       constrain $ d3 .< literal Thursday

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
