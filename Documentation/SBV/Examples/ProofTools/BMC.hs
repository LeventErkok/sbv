-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.ProofTools.BMC
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A BMC example, showing how traditional state-transition reachability
-- problems can be coded using SBV, using bounded model checking.
--
-- We imagine a system with two integer variables, @x@ and @y@. At each
-- iteration, we can either increment @x@ by @2@, or decrement @y@ by @4@.
--
-- Can we reach a state where @x@ and @y@ are the same starting from @x=0@
-- and @y=10@?
--
-- What if @y@ starts at @11@?
-----------------------------------------------------------------------------

{-# LANGUAGE NamedFieldPuns #-}

module Documentation.SBV.Examples.ProofTools.BMC where

import Data.SBV
import Data.SBV.Tools.BMC
import Data.SBV.Control

-- * System state

-- | System state, containing the two integers.
data S = S { x :: SInteger, y :: SInteger }

-- | Symbolic equality for @S@.
instance EqSymbolic S where
   S {x = x1, y = y1} .== S {x = x2, y = y2} = x1 .== x2 .&& y1 .== y2

-- * Encoding the problem

-- | We parameterize over the initial state for different variations.
problem :: Int -> (S -> SBool) -> IO (Either String (Int, [(Integer, Integer)]))
problem lim initial = bmc (Just lim) True setup fresh extract initial trans goal
  where
        -- This is where we would put solver options, typically via
        -- calls to 'Data.SBV.setOption'. We do not need any for this problem,
        -- so we simply do nothing.
        setup :: Symbolic ()
        setup = return ()

        -- Getting a new state:
        fresh :: Query S
        fresh = S <$> freshVar_ <*> freshVar_

        -- Extracting the state into what we want to observe
        extract :: S -> Query (Integer, Integer)
        extract S{x, y} = (,) <$> getValue x <*> getValue y

        -- Transition relation: At each step we either
        -- get to increase @x@ by 2, or decrement @y@ by 4:
        trans :: S -> [S]
        trans S{x, y} = [ S { x = x + 2, y = y     }
                        , S { x = x,     y = y - 4 }
                        ]

        -- Goal state is when @x@ equals @y@:
        goal :: S -> SBool
        goal S{x, y} = x .== y

-- * Examples

-- | Example 1: We start from @x=0@, @y=10@, and search up to depth @10@. We have:
--
-- >>> ex1
-- BMC: Iteration: 0
-- BMC: Iteration: 1
-- BMC: Iteration: 2
-- BMC: Iteration: 3
-- BMC: Solution found at iteration 3
-- Right (3,[(0,10),(0,6),(0,2),(2,2)])
--
-- As expected, there's a solution in this case. Furthermore, since the BMC engine
-- found a solution at depth @3@, we also know that there is no solution at
-- depths @0@, @1@, or @2@; i.e., this is "a" shortest solution. (That is,
-- it may not be unique, but there isn't a shorter sequence to get us to
-- our goal.)
ex1 :: IO (Either String (Int, [(Integer, Integer)]))
ex1 = problem 10 isInitial
  where isInitial :: S -> SBool
        isInitial S{x, y} = x .== 0 .&& y .== 10

-- | Example 2: We start from @x=0@, @y=11@, and search up to depth @10@. We have:
--
-- >>> ex2
-- BMC: Iteration: 0
-- BMC: Iteration: 1
-- BMC: Iteration: 2
-- BMC: Iteration: 3
-- BMC: Iteration: 4
-- BMC: Iteration: 5
-- BMC: Iteration: 6
-- BMC: Iteration: 7
-- BMC: Iteration: 8
-- BMC: Iteration: 9
-- Left "BMC limit of 10 reached"
--
-- As expected, there's no solution in this case. While SBV (and BMC) cannot establish
-- that there is no solution at a larger depth, you can see that this will never be the
-- case: In each step we do not change the parity of either variable. That is, @x@
-- will remain even, and @y@ will remain odd. So, there will never be a solution at
-- any depth. This isn't the only way to see this result of course, but the point
-- remains that BMC is just not capable of establishing inductive facts.
ex2 :: IO (Either String (Int, [(Integer, Integer)]))
ex2 = problem 10 isInitial
  where isInitial :: S -> SBool
        isInitial S{x, y} = x .== 0 .&& y .== 11
