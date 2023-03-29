-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Optimization.LinearOpt
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Simple linear optimization example, as found in operations research texts.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Optimization.LinearOpt where

import Data.SBV

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV

-- | Taken from <http://people.brunel.ac.uk/~mastjjb/jeb/or/morelp.html>
--
--    *  maximize 5x1 + 6x2
--       - subject to
--
--          1. x1 + x2 <= 10
--          2. x1 - x2 >= 3
--          3. 5x1 + 4x2 <= 35
--          4. x1 >= 0
--          5. x2 >= 0
--
-- >>> optimize Lexicographic problem
-- Optimal model:
--   x1   =  47 % 9 :: Real
--   x2   =  20 % 9 :: Real
--   goal = 355 % 9 :: Real
problem :: ConstraintSet
problem = do [x1, x2] <- mapM sReal ["x1", "x2"]

             constrain $ x1 + x2 .<= 10
             constrain $ x1 - x2 .>= 3
             constrain $ 5*x1 + 4*x2 .<= 35
             constrain $ x1 .>= 0
             constrain $ x2 .>= 0

             maximize "goal" $ 5 * x1 + 6 * x2
