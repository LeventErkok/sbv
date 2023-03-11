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

{-# LANGUAGE OverloadedLists  #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Misc.Definitions where

import Data.SBV
import Data.SBV.Tuple
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
sumToN = smtFunction "sumToN" $ \x -> ite (x .<= 0) 0 (x + sumToN (x - 1))

-- | Prove that sumToN works as expected.
--
-- We have:
--
-- >>> sumToNExample
-- Satisfiable. Model:
--   s0 =  5 :: Integer
--   s1 = 15 :: Integer
sumToNExample :: IO SatResult
sumToNExample = sat $ \a r -> a .== 5 .&& r .== sumToN a

-- | Coding list-length recursively. Again, we map directly to an SMTLib function.
len :: SList Integer -> SInteger
len = smtFunction "list_length" $ \xs -> ite (L.null xs) 0 (1 + len (L.tail xs))

-- | Calculate the length of a list, using recursive functions.
--
-- We have:
--
-- >>> lenExample
-- Satisfiable. Model:
--   s0 = [1,2,3] :: [Integer]
--   s1 =       3 :: Integer
lenExample :: IO SatResult
lenExample = sat $ \a r -> a .== [1,2,3::Integer] .&& r .== len a

-- | Mutually recursive definitions. The trick is to define the functions together, and pull the results out individually.
isEvenOdd :: SInteger -> STuple Bool Bool
isEvenOdd = smtFunction "isEvenOdd" $ \x ->
                  ite (x .<  0) (isEvenOdd (-x))
                $ ite (x .== 0) (tuple (sTrue, sFalse))
                                (swap (isEvenOdd (x - 1)))

-- | Extract the isEven function for easier use.
isEven :: SInteger -> SBool
isEven x = isEvenOdd x ^._1

-- | Extract the isEven function for easier use.
isOdd :: SInteger -> SBool
isOdd x = isEvenOdd x ^._2

-- | Prove that 20 is even.
--
-- We have:
-- >>> mutRecExample
-- Satisfiable. Model:
--   s0 =   20 :: Integer
--   s1 = True :: Bool
--
-- Note that we would love to prove things of the form:
--
-- @
--   proveWith z3{verbose=True} $ \x -> isEven x .|| isOdd x
-- @
--
-- alas, if you try this you'll see that z3 goes on forever. Such proofs require induction
-- and SMT-solvers do not do induction out-of-the box, at least not yet!
mutRecExample :: IO SatResult
mutRecExample = sat $ \a r -> a .== 20 .&& r .== isEven a
