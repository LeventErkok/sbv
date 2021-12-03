-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Misc.Definitions
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrates how we can add actual SMT-definitions for functions
-- that cannot otherwise be defined in SBV. Typically, these are used
-- for recursive definitions.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Misc.Definitions where

import Data.SBV

-- | Sum of numbers from 0 to the given number.
-- Note that this cannot be defined as a regular Haskell function, as
-- it wouldn't terminate as it recurses on a symbolic argument.
sumToN :: SInteger -> SInteger
sumToN = uninterpret "sumToN"

-- | Add the definition of sum to the SMT solver. Note that SBV
-- performs no checks on your definition, neither that it is
-- well formed, or even has the correct type!
defineSum :: Symbolic ()
defineSum = addSMTDefinition "sumToN"
                [ "(define-fun-rec sumToN ((x Int)) Int"
                , "                (ite (<= x 0)"
                , "                     0"
                , "                     (+ x (sumToN (- x 1)))))"
                ]

-- | A simple proof using 'sumToN'. We get a failure, because we haven't
-- given the solver the definition, and thus it goes completely uninterpreted.
--
-- We have:
--
-- >>> badExample
-- Falsifiable. Counter-example:
--   sumToN :: Integer -> Integer
--   sumToN _ = 0
--
-- Since 'sumToN' remains uninterpreted, the solver gave us a model that obviously
-- fails the property.
badExample :: IO ThmResult
badExample = prove $ do
        let check = sumToN 5 .== 15  -- Should fail, even though 5*6/2 = 15
        pure check :: Predicate

-- | Same example, except this time we give the solver the definition of the function,
-- and thus the proof goes through.
--
-- We have:
--
-- >>> goodExample
-- Q.E.D.
--
-- In this case, the solver has the definition, and proves the predicate as expected.
goodExample :: IO ThmResult
goodExample = prove $ do
        defineSum
        let check = sumToN 5 .== 15  -- Should fail, even though 5*6/2 = 15
        pure check :: Predicate
