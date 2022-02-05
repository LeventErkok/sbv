-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.ProofTools.Sum
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Example inductive proof to show partial correctness of the traditional
-- for-loop sum algorithm:
--
-- @
--     s = 0
--     i = 0
--     while i <= n:
--        s += i
--        i++
-- @
--
-- We prove the loop invariant and establish partial correctness that
-- @s@ is the sum of all numbers up to and including @n@ upon termination.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.ProofTools.Sum where

import Data.SBV
import Data.SBV.Tools.Induction
import Data.SBV.Control

import GHC.Generics hiding (S)

-- * System state

-- | System state. We simply have two components, parameterized
-- over the type so we can put in both concrete and symbolic values.
data S a = S { s :: a, i :: a, n :: a } deriving (Show, Mergeable, Generic, Functor, Foldable, Traversable)

-- | 'Fresh' instance for our state
instance Fresh IO (S SInteger) where
  fresh  = S <$> freshVar_  <*> freshVar_  <*> freshVar_

-- | Encoding partial correctness of the sum algorithm. We have:
--
-- >>> sumCorrect
-- Q.E.D.
sumCorrect :: IO (InductionResult (S Integer))
sumCorrect = induct chatty setup initial trans strengthenings inv goal
  where -- Set this to True for SBV to print steps as it proceeds
        -- through the inductive proof
        chatty :: Bool
        chatty = False

        -- This is where we would put solver options, typically via
        -- calls to 'Data.SBV.setOption'. We do not need any for this problem,
        -- so we simply do nothing.
        setup :: Symbolic ()
        setup = return ()

        -- Initially, @s@ and @i@ are both @0@. We also require @n@ to be at least @0@.
        initial :: S SInteger -> SBool
        initial S{s, i, n} = s .== 0 .&& i .== 0 .&& n .>= 0

        -- We code the algorithm almost literally in SBV notation:
        trans :: S SInteger -> [S SInteger]
        trans st@S{s, i, n} = [ite (i .<= n)
                                   st { s = s+i, i = i+1 }
                                   st
                              ]

        -- No strengthenings needed for this problem!
        strengthenings :: [(String, S SInteger -> SBool)]
        strengthenings = []

        -- Loop invariant: @i@ remains at most @n+1@ and @s@ the sum of
        -- all the numbers up-to @i-1@.
        inv :: S SInteger -> SBool
        inv S{s, i, n} =    i .<= n+1
                        .&& s .== (i * (i - 1)) `sDiv` 2

        -- Final goal. When the termination condition holds, the sum is
        -- equal to all the numbers up to and including @n@. Note that
        -- SBV does not prove the termination condition; it simply is
        -- the indication that the loop has ended as specified by the user.
        goal :: S SInteger -> (SBool, SBool)
        goal S{s, i, n} = (i .== n+1, s .== (n * (n+1)) `sDiv` 2)
