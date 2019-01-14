-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.ProofTools.Fibonacci
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Example inductive proof to show partial correctness of the for-loop
-- based fibonacci algorithm:
--
-- @
--     i = 0
--     k = 1
--     m = 0
--     while i < n:
--        m, k = k, m + k
--        i++
-- @
--
-- We do the proof against an axiomatized fibonacci implementation using an
-- uninterpreted function.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}

module Documentation.SBV.Examples.ProofTools.Fibonacci where

import Data.SBV
import Data.SBV.Tools.Induction
import Data.SBV.Control

import GHC.Generics hiding (S)

-- * System state

-- | System state. We simply have two components, parameterized
-- over the type so we can put in both concrete and symbolic values.
data S a = S { i :: a, k :: a, m :: a, n :: a }
         deriving (Show, Mergeable, Generic)

-- | Make our state queriable
instance Queriable IO (S SInteger) (S Integer) where
   fresh = S <$> freshVar_ <*> freshVar_ <*> freshVar_ <*> freshVar_
   extract S{i, k, m, n} = S <$> getValue i <*> getValue k <*> getValue m <*> getValue n

-- | Encoding partial correctness of the sum algorithm. We have:
--
-- >>> fibCorrect
-- Q.E.D.
--
-- NB. In my experiments, I found that this proof is quite fragile due
-- to the use of quantifiers: If you make a mistake in your algorithm
-- or the coding, z3 pretty much spins forever without finding a counter-example.
-- However, with the correct coding, the proof is almost instantaneous!
fibCorrect :: IO (InductionResult (S Integer))
fibCorrect = induct chatty setup initial trans strengthenings inv goal
  where -- Set this to True for SBV to print steps as it proceeds
        -- through the inductive proof
        chatty :: Bool
        chatty = False

        -- Declare fib as un uninterpreted function:
        fib :: SInteger -> SInteger
        fib = uninterpret "fib"

        -- We setup to axiomatize the textbook definition of fib in SMT-Lib
        setup :: Symbolic ()
        setup = do constrain $ fib 0 .== 0
                   constrain $ fib 1 .== 1

                   -- This is unfortunate; but SBV currently does not support
                   -- adding quantified constraints in the query mode. So we
                   -- have to write this axiom in SMT-Lib. Note also how carefully
                   -- we've chosen this axiom to work with our proof!
                   addAxiom "fib_n" [ "(assert (forall ((x Int))"
                                    , "                (= (fib (+ x 2)) (+ (fib (+ x 1)) (fib x)))))"
                                    ]

        -- Initialize variables
        initial :: S SInteger -> SBool
        initial S{i, k, m, n} = i .== 0 .&& k .== 1 .&& m .== 0 .&& n .>= 0

        -- We code the algorithm almost literally in SBV notation:
        trans :: S SInteger -> [S SInteger]
        trans st@S{i, k, m, n} = [ite (i .< n)
                                      st { i = i + 1, k = m + k, m = k }
                                      st
                                 ]

        -- No strengthenings needed for this problem!
        strengthenings :: [(String, S SInteger -> SBool)]
        strengthenings = []

        -- Loop invariant: @i@ remains at most @n@, @k@ is @fib (i+1)@
        -- and @m@ is fib(i)@:
        inv :: S SInteger -> SBool
        inv S{i, k, m, n} =    i .<= n
                           .&& k .== fib (i+1)
                           .&& m .== fib i

        -- Final goal. When the termination condition holds, the value @m@
        -- holds the @n@th fibonacc number. Note that SBV does not prove the
        -- termination condition; it simply is the indication that the loop
        -- has ended as specified by the user.
        goal :: S SInteger -> (SBool, SBool)
        goal S{i, m, n} = (i .== n, m .== fib n)
