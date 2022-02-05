-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.ProofTools.Strengthen
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- An example showing how traditional state-transition invariance problems
-- can be coded using SBV, using induction. We also demonstrate the use of
-- invariant strengthening.
--
-- This example comes from Bradley's [Understanding IC3](http://theory.stanford.edu/~arbrad/papers/Understanding_IC3.pdf) paper,
-- which considers the following two programs:
--
-- @
--      x, y := 1, 1                    x, y := 1, 1
--      while *:                        while *:
--        x, y := x+1, y+x                x, y := x+y, y+x
-- @
--
-- Where @*@ stands for non-deterministic choice. For each program we try to prove that @y >= 1@ is an invariant.
--
-- It turns out that the property @y >= 1@ is indeed an invariant, but is
-- not inductive for either program. We proceed to strengten the invariant
-- and establish it for the first case. We then note that the same strengthening
-- doesn't work for the second program, and find a further strengthening to
-- establish that case as well. This example follows the introductory example
-- in Bradley's paper quite closely.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.ProofTools.Strengthen where

import Data.SBV
import Data.SBV.Tools.Induction
import Data.SBV.Control

-- * System state

-- | System state. We simply have two components, parameterized
-- over the type so we can put in both concrete and symbolic values.
data S a = S { x :: a, y :: a }
         deriving (Show, Functor, Foldable, Traversable)

-- | 'Fresh' instance for our state
instance Fresh IO (S SInteger) where
  fresh = S <$> freshVar_ <*> freshVar_

-- * Encoding the problem

-- | We parameterize over the transition relation and the strengthenings to
-- investigate various combinations.
problem :: (S SInteger -> [S SInteger]) -> [(String, S SInteger -> SBool)] -> IO (InductionResult (S Integer))
problem trans strengthenings = induct chatty setup initial trans strengthenings inv goal
  where -- Set this to True for SBV to print steps as it proceeds
        -- through the inductive proof
        chatty :: Bool
        chatty = False

        -- This is where we would put solver options, typically via
        -- calls to 'Data.SBV.setOption'. We do not need any for this problem,
        -- so we simply do nothing.
        setup :: Symbolic ()
        setup = return ()

        -- Initially, @x@ and @y@ are both @1@
        initial :: S SInteger -> SBool
        initial S{x, y} = x .== 1 .&& y .== 1

        -- Invariant to prove:
        inv :: S SInteger -> SBool
        inv S{y} = y .>= 1

        -- We're not interested in termination/goal for this problem, so just pass trivial values
        goal :: S SInteger -> (SBool, SBool)
        goal _ = (sTrue, sTrue)

-- | The first program, coded as a transition relation:
pgm1 :: S SInteger -> [S SInteger]
pgm1 S{x, y} = [S{x = x+1, y = y+x}]

-- | The second program, coded as a transition relation:
pgm2 :: S SInteger -> [S SInteger]
pgm2 S{x, y} = [S{x = x+y, y = y+x}]

-- * Examples

-- | Example 1: First program, with no strengthenings. We have:
--
-- >>> ex1
-- Failed while establishing consecution.
-- Counter-example to inductiveness:
--   S {x = -1, y = 1}
ex1 :: IO (InductionResult (S Integer))
ex1 = problem pgm1 strengthenings
  where strengthenings :: [(String, S SInteger -> SBool)]
        strengthenings = []

-- | Example 2: First program, strengthened with @x >= 0@. We have:
--
-- >>> ex2
-- Q.E.D.
ex2 :: IO (InductionResult (S Integer))
ex2 = problem pgm1 strengthenings
  where strengthenings :: [(String, S SInteger -> SBool)]
        strengthenings = [("x >= 0", \S{x} -> x .>= 0)]

-- | Example 3: Second program, with no strengthenings. We have:
--
-- >>> ex3
-- Failed while establishing consecution.
-- Counter-example to inductiveness:
--   S {x = -1, y = 1}
ex3 :: IO (InductionResult (S Integer))
ex3 = problem pgm2 strengthenings
  where strengthenings :: [(String, S SInteger -> SBool)]
        strengthenings = []

-- | Example 4: Second program, strengthened with @x >= 0@. We have:
--
-- >>> ex4
-- Failed while establishing consecution for strengthening "x >= 0".
-- Counter-example to inductiveness:
--   S {x = 0, y = -1}
ex4 :: IO (InductionResult (S Integer))
ex4 = problem pgm2 strengthenings
  where strengthenings :: [(String, S SInteger -> SBool)]
        strengthenings = [("x >= 0", \S{x} -> x .>= 0)]

-- | Example 5: Second program, strengthened with @x >= 0@ and @y >= 1@ separately. We have:
--
-- >>> ex5
-- Failed while establishing consecution for strengthening "x >= 0".
-- Counter-example to inductiveness:
--   S {x = 0, y = -1}
--
-- Note how this was sufficient in 'ex2' to establish the invariant for the first
-- program, but fails for the second.
ex5 :: IO (InductionResult (S Integer))
ex5 = problem pgm2 strengthenings
  where strengthenings :: [(String, S SInteger -> SBool)]
        strengthenings = [ ("x >= 0", \S{x} -> x .>= 0)
                         , ("y >= 1", \S{y} -> y .>= 1)
                         ]

-- | Example 6: Second program, strengthened with @x >= 0 \/\\ y >= 1@ simultaneously. We have:
--
-- >>> ex6
-- Q.E.D.
--
-- Compare this to 'ex5'. As pointed out by Bradley, this shows that
-- /a conjunction of assertions can be inductive when none of its components, on its own, is inductive./
-- It remains an art to find proper loop invariants, though the science is improving!
ex6 :: IO (InductionResult (S Integer))
ex6 = problem pgm2 strengthenings
  where strengthenings :: [(String, S SInteger -> SBool)]
        strengthenings = [("x >= 0 /\\ y >= 1", \S{x, y} -> x .>= 0 .&& y .>= 1)]
