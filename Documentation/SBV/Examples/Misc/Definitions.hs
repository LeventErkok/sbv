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

{-# LANGUAGE OverloadedLists #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Misc.Definitions where

import Data.SBV
import qualified Data.SBV.List as L

-- | Add one to an argument
add1 :: SInteger -> SInteger
add1 = smtFunction "add1" (+1)

-- | Reverse run the add1 function. Note that the generated SMTLib will have the function
-- add1 itself defined. You can verify this by running the below in verbose mode.
--
-- >>> add1Example
-- Satisfiable. Model:
--   x = 4 :: Integer
add1Example :: IO SatResult
add1Example = sat $ do
        x <- sInteger "x"
        pure $ 5 .== add1 x

-- | Sum of numbers from 0 to the given number. Since this is a recursive
-- definition, we cannot simply symbolically simulate it as it wouldn't
-- terminat. So, we use the function generation facilities to define it
-- directly in SMTLib. Note how the function itself takes a "recursive version"
-- of itself, and all recursive calls are made with this name.
sumToN :: SInteger -> SInteger
sumToN = smtRecFunction "sumToN" f
  where f rF x = ite (x .<= 0) 0 (x + rF (x - 1))

-- | Prove that sumToN works as expected.
--
-- We have:
--
-- >>> recExample
-- Satisfiable. Model:
--   s0 = 15 :: Integer
recExample :: IO SatResult
recExample = sat $ (.== sumToN 5)

-- | Coding list-length recursively. Again, we map directly to an SMTLib function.
len :: SList Integer -> SInteger
len = smtRecFunction "list_length" f
  where f rF xs = ite (L.null xs) 0 (1 + rF (L.tail xs))

-- | Calculate the length of a list, using recursive functions.
--
-- We have:
--
-- >>> lenExample
-- Satisfiable. Model:
--   s0 = 3 :: Integer
lenExample :: IO SatResult
lenExample = sat $ (.== len [1,2,3::Integer])
