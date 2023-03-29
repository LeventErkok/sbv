-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Optimization.Production
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Solves a simple linear optimization problem
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Optimization.Production where

import Data.SBV

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV

-- | Taken from <http://people.brunel.ac.uk/~mastjjb/jeb/or/morelp.html>
--
-- A company makes two products (X and Y) using two machines (A and B).
--
--   - Each unit of X that is produced requires 50 minutes processing time on machine
--     A and 30 minutes processing time on machine B.
--
--   - Each unit of Y that is produced requires 24 minutes processing time on machine
--     A and 33 minutes processing time on machine B.
--
--   - At the start of the current week there are 30 units of X and 90 units of Y in stock.
--     Available processing time on machine A is forecast to be 40 hours and on machine B is
--     forecast to be 35 hours.
--
--   - The demand for X in the current week is forecast to be 75 units and for Y is forecast
--     to be 95 units.
--
--   - Company policy is to maximise the combined sum of the units of X and the units of Y
--     in stock at the end of the week.
--
-- How much of each product should we make in the current week?
--
-- We have:
--
-- >>> optimize Lexicographic production
-- Optimal model:
--   X     = 45 :: Integer
--   Y     =  6 :: Integer
--   stock =  1 :: Integer
--
-- That is, we should produce 45 X's and 6 Y's, with the final maximum stock of just 1 expected!
production :: ConstraintSet
production = do x <- sInteger "X" -- Units of X produced
                y <- sInteger "Y" -- Units of X produced

                -- Amount of time on machine A and B
                let timeA = 50 * x + 24 * y
                    timeB = 30 * x + 33 * y

                constrain $ timeA .<= 40 * 60
                constrain $ timeB .<= 35 * 60

                -- Amount of product we'll end up with
                let finalX = x + 30
                    finalY = y + 90

                -- Make sure the demands are met:
                constrain $ finalX .>= 75
                constrain $ finalY .>= 95

                -- Policy: Maximize the final stock
                maximize "stock" $ (finalX - 75) + (finalY - 95)
