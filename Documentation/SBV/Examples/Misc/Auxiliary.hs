-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Misc.Auxiliary
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrates model construction with auxiliary variables. Sometimes we
-- need to introduce a variable in our problem as an existential variable,
-- but it's "internal" to the problem and we do not consider it as part of
-- the solution. Also, in an `allSat` scenario, we may not care for models
-- that only differ in these auxiliaries. SBV allows designating such variables
-- as `isNonModelVar` so we can still use them like any other variable, but without
-- considering them explicitly in model construction.
-----------------------------------------------------------------------------

{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Misc.Auxiliary where

import Data.SBV

-- | A simple predicate, based on two variables @x@ and @y@, true when
-- @0 <= x <= 1@ and @x - abs y@ is @0@.
problem :: Predicate
problem = do x <- free "x"
             y <- free "y"
             constrain $ x .>= 0
             constrain $ x .<= 1
             return $ x - abs y .== (0 :: SInteger)

-- | Generate all satisfying assignments for our problem. We have:
--
-- >>> allModels
-- Solution #1:
--   x =  1 :: Integer
--   y = -1 :: Integer
-- Solution #2:
--   x = 1 :: Integer
--   y = 1 :: Integer
-- Solution #3:
--   x = 0 :: Integer
--   y = 0 :: Integer
-- Found 3 different solutions.
--
-- Note that solutions @2@ and @3@ share the value @x = 1@, since there are
-- multiple values of @y@ that make this particular choice of @x@ satisfy our constraint.
allModels :: IO AllSatResult
allModels = allSat problem

-- | Generate all satisfying assignments, but we first tell SBV that @y@ should not be considered
-- as a model problem, i.e., it's auxiliary. We have:
--
-- >>> modelsWithYAux
-- Solution #1:
--   x = 1 :: Integer
-- Solution #2:
--   x = 0 :: Integer
-- Found 2 different solutions.
--
-- Note that we now have only two solutions, one for each unique value of @x@ that satisfy our
-- constraint.
modelsWithYAux :: IO AllSatResult
modelsWithYAux = allSatWith z3{isNonModelVar = (`elem` ["y"])} problem
