-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Misc.SoftConstrain
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrates soft-constraints, i.e., those that the solver
-- is free to leave unsatisfied. Solvers will try to satisfy
-- this constraint, unless it is impossible to do so to get
-- a model. Can be good in modeling default values, for instance.
-----------------------------------------------------------------------------

{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Misc.SoftConstrain where

import Data.SBV

-- | Create two strings, requiring one to be a particular value, constraining the other
-- to be different than another constant string. But also add soft constraints to
-- indicate our preferences for each of these variables. We get:
--
-- >>> example
-- Satisfiable. Model:
--   x = "x-must-really-be-hello" :: String
--   y =        "default-y-value" :: String
--
-- Note how the value of @x@ is constrained properly and thus the default value
-- doesn't kick in, but @y@ takes the default value since it is acceptable by
-- all the other hard constraints.
example :: IO SatResult
example = sat $ do x <- sString "x"
                   y <- sString "y"

                   constrain $ x .== "x-must-really-be-hello"
                   constrain $ y ./= "y-can-be-anything-but-hello"

                   -- Now add soft-constraints to indicate our preference
                   -- for what these variables should be:
                   softConstrain $ x .== "default-x-value"
                   softConstrain $ y .== "default-y-value"

                   return sTrue
