-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Optimization.ExtField
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrates the extension field (@oo@/@epsilon@) optimization results.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Optimization.ExtField where

import Data.SBV

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV

-- | Optimization goals where min/max values might require assignments
-- to values that are infinite (integer case), or infinite/epsilon (real case).
-- This simple example demonstrates how SBV can be used to extract such values.
--
-- We have:
--
-- >>> optimize Independent problem
-- Objective "one-x": Optimal in an extension field:
--   one-x =  oo :: Integer
--   min_y = 7.0 :: Real
--   min_z = 5.0 :: Real
-- Objective "min_y": Optimal in an extension field:
--   one-x =  oo :: Integer
--   min_y = 7.0 :: Real
--   min_z = 5.0 :: Real
-- Objective "min_z": Optimal in an extension field:
--   one-x =  oo :: Integer
--   min_y = 7.0 :: Real
--   min_z = 5.0 :: Real
problem :: ConstraintSet
problem = do x <- sInteger "x"
             y <- sReal "y"
             z <- sReal "z"

             maximize "one-x" $ 1 - x

             constrain $ y .>= 0 .&& z .>= 5
             minimize "min_y" $ 2+y+z

             minimize "min_z" z
