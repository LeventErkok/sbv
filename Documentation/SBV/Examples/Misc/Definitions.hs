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

-------------------------------------------------------------------------
-- * Simple functions
-------------------------------------------------------------------------

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

-------------------------------------------------------------------------
-- * Basic recursive functions
-------------------------------------------------------------------------

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

-------------------------------------------------------------------------
-- * Mutual recursion
-------------------------------------------------------------------------

-- | A simple mutual-recursion example, from the z3 documentation. We have:
--
-- >>> pingPong
-- Satisfiable. Model:
--   s0 = 1 :: Integer
pingPong :: IO SatResult
pingPong = sat $ \x -> x .> 0 .&& ping x sTrue .> x
  where ping :: SInteger -> SBool -> SInteger
        ping = smtFunction "ping" $ \x y -> ite y (pong (x+1) (sNot y)) (x - 1)

        pong :: SInteger -> SBool -> SInteger
        pong = smtFunction "pong" $ \a b -> ite b (ping (a-1) (sNot b)) a

-- | Usual way to define even-odd mutually recursively. Unfortunately, while this goes through,
-- the backend solver does not terminate on this example. See 'evenOdd2' for an alternative
-- technique to handle such definitions, which seems to be more solver friendly.
evenOdd :: IO SatResult
evenOdd = satWith z3{verbose=True} $ \a r -> a .== 20 .&& r .== isE a
  where isE, isO :: SInteger -> SBool
        isE = smtFunction "isE" $ \x -> ite (x .< 0) (isE (-x)) (x .== 0 .|| isO  (x - 1))
        isO = smtFunction "isO"  $ \x -> ite (x .< 0) (isO  (-x)) (x .== 0 .|| isE (x - 1))

-- | Another technique to handle mutually definitions is to define the functions together, and pull the results out individually.
-- This usually works better than defining the functions separately, from a solver perspective.
isEvenOdd :: SInteger -> STuple Bool Bool
isEvenOdd = smtFunction "isEvenOdd" $ \x -> ite (x .<  0) (isEvenOdd (-x))
                                          $ ite (x .== 0) (tuple (sTrue, sFalse))
                                                          (swap (isEvenOdd (x - 1)))

-- | Extract the isEven function for easier use.
isEven :: SInteger -> SBool
isEven x = isEvenOdd x ^._1

-- | Extract the isOdd function for easier use.
isOdd :: SInteger -> SBool
isOdd x = isEvenOdd x ^._2

-- | We can prove 20 is even and definitely not odd, thusly:
--
-- >>> evenOdd2
-- Satisfiable. Model:
--   s0 =    20 :: Integer
--   s1 =  True :: Bool
--   s2 = False :: Bool
evenOdd2 :: IO SatResult
evenOdd2 = sat $ \a r1 r2 -> a .== 20 .&& r1 .== isEven a .&& r2 .== isOdd a

-------------------------------------------------------------------------
-- * Nested recursion
-------------------------------------------------------------------------

-- | Ackermann function, demonstrating nested recursion.
ack :: SInteger -> SInteger -> SInteger
ack = smtFunction "ack" $ \x y -> ite (x .== 0) (y + 1)
                                $ ite (y .== 0) (ack (x - 1) 1)
                                                (ack (x - 1) (ack x (y - 1)))

-- | We can prove constant-folding instances of the equality @ack 1 y == y + 2@:
--
-- >>> ack1y
-- Satisfiable. Model:
--   s0 = 5 :: Integer
--   s1 = 7 :: Integer
--
-- Expecting the prover to handle the general case for arbitrary @y@ is beyond the current
-- scope of what SMT solvers do out-of-the-box for the time being.
ack1y :: IO SatResult
ack1y = sat $ \y r -> y .== 5 .&& r .== ack 1 y
