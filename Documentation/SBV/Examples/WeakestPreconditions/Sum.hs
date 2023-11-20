-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.WeakestPreconditions.Sum
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proof of correctness of an imperative summation algorithm, using weakest
-- preconditions. We investigate a few different invariants and see how
-- different versions lead to proofs and failures.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.WeakestPreconditions.Sum where

import Data.SBV
import Data.SBV.Control

import Data.SBV.Tools.WeakestPreconditions

import GHC.Generics (Generic)

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV

-- * Program state

-- | The state for the sum program, parameterized over a base type @a@.
data SumS a = SumS { n :: a    -- ^ The input value
                   , i :: a    -- ^ Loop counter
                   , s :: a    -- ^ Running sum
                   }
                   deriving (Show, Generic, Mergeable, Functor, Foldable, Traversable)

-- | Show instance for 'SumS'. The above deriving clause would work just as well,
-- but we want it to be a little prettier here, and hence the @OVERLAPS@ directive.
instance {-# OVERLAPS #-} (SymVal a, Show a) => Show (SumS (SBV a)) where
   show (SumS n i s) = "{n = " ++ sh n ++ ", i = " ++ sh i ++ ", s = " ++ sh s ++ "}"
     where sh v = maybe "<symbolic>" show (unliteral v)

-- | 'Fresh' instance for the program state
instance SymVal a => Fresh IO (SumS (SBV a)) where
  fresh = SumS <$> freshVar_  <*> freshVar_  <*> freshVar_

-- | Helper type synonym
type S = SumS SInteger

-- * The algorithm

-- | The imperative summation algorithm:
--
-- @
--    i = 0
--    s = 0
--    while i < n
--      i = i+1
--      s = s+i
-- @
--
-- Note that we need to explicitly annotate each loop with its invariant and the termination
-- measure. For convenience, we take those two as parameters, so we can experiment later.
algorithm :: Invariant S -> Maybe (Measure S) -> Stmt S
algorithm inv msr = Seq [ Assign $ \st -> st{i = 0, s = 0}
                        , assert "n >= 0" $ \SumS{n} -> n .>= 0
                        , While "i < n"
                                inv
                                msr
                                (\SumS{i, n} -> i .< n)
                                $ Seq [ Assign $ \st@SumS{i}    -> st{i = i+1}
                                      , Assign $ \st@SumS{i, s} -> st{s = s+i}
                                      ]
                        ]

-- | Precondition for our program: @n@ must be non-negative. Note that there is
-- an explicit call to 'Data.SBV.Tools.WeakestPreconditions.abort' in our program to protect against this case, so
-- if we do not have this precondition, all programs will fail.
pre :: S -> SBool
pre SumS{n} = n .>= 0

-- | Postcondition for our program: @s@ must be the sum of all numbers up to
-- and including @n@.
post :: S -> SBool
post SumS{n, s} = s .== (n * (n+1)) `sDiv` 2

-- | Stability condition: Program must leave @n@ unchanged.
noChange :: Stable S
noChange = [stable "n" n]

-- | A program is the algorithm, together with its pre- and post-conditions.
imperativeSum :: Invariant S -> Maybe (Measure S) -> Program S
imperativeSum inv msr = Program { setup         = return ()
                                , precondition  = pre
                                , program       = algorithm inv msr
                                , postcondition = post
                                , stability     = noChange
                                }

-- * Correctness

-- | Check that the program terminates and @s@ equals @n*(n+1)/2@
-- upon termination, i.e., the sum of all numbers upto @n@. Note
-- that this only holds if @n >= 0@ to start with, as guaranteed
-- by the precondition of our program.
--
-- The correct termination measure is @n-i@: It goes down in each
-- iteration provided we start with @n >= 0@ and it always remains
-- non-negative while the loop is executing. Note that we do not
-- need a lexicographic measure in this case, hence we simply return
-- a list of one element.
--
-- The correct invariant is a conjunction of two facts. First, @s@ is
-- equivalent to the sum of numbers @0@ upto @i@.  This clearly holds at
-- the beginning when @i = s = 0@, and is maintained in each iteration
-- of the body. Second, it always holds that @i <= n@ as long as the
-- loop executes, both before and after each execution of the body.
-- When the loop terminates, it holds that @i = n@. Since the invariant says
-- @s@ is the sum of all numbers up to but not including @i@, we
-- conclude that @s@ is the sum of all numbers up to and including @n@,
-- as requested.
--
-- Note that coming up with this invariant is neither trivial, nor easy
-- to automate by any means. What SBV provides is a way to check that
-- your invariant and termination measures are correct, not
-- a means of coming up with them in the first place.
--
-- We have:
--
-- >>> :set -XNamedFieldPuns
-- >>> let invariant SumS{n, i, s} = s .== (i*(i+1)) `sDiv` 2 .&& i .<= n
-- >>> let measure   SumS{n, i}    = [n - i]
-- >>> correctness invariant (Just measure)
-- Total correctness is established.
-- Q.E.D.
correctness :: Invariant S -> Maybe (Measure S) -> IO (ProofResult (SumS Integer))
correctness inv msr = wpProveWith defaultWPCfg{wpVerbose=True} (imperativeSum inv msr)

-- * Example proof attempts
--
-- $examples

{- $examples
It is instructive to look at several proof attempts to see what can go wrong and how
the weakest-precondition engine behaves.

== Always false invariant

Let's see what happens if we have an always false invariant. Clearly, this will not
do the job, but it is instructive to see the output. For this exercise, we are only
interested in partial correctness (to see the impact of the invariant only), so we
will simply use 'Nothing' for the measures.

>>> import Control.Monad (void)
>>> let invariant _ = sFalse
>>> void $ correctness invariant Nothing
Following proof obligation failed:
==================================
  Invariant for loop "i < n" fails upon entry:
    SumS {n = 0, i = 0, s = 0}

When the invariant is constant false, it fails upon entry to the loop, and thus the
proof itself fails.

== Always true invariant

The invariant must hold prior to entry to the loop, after the loop-body
executes, and must be strong enough to establish the postcondition. The easiest
thing to try would be the invariant that always returns true:

>>> let invariant _ = sTrue
>>> void $ correctness invariant Nothing
Following proof obligation failed:
==================================
  Postcondition fails:
    Start: SumS {n = 0, i = 0, s = 0}
    End  : SumS {n = 0, i = 0, s = 1}

In this case, we are told that the end state does not establish the
post-condition. Indeed when @n=0@, we would expect @s=0@, not @s=1@.

The natural question to ask is how did SBV come up with this unexpected
state at the end of the program run? If you think about the program execution, indeed this
state is unreachable: We know that @s@ represents the sum of all numbers up to @i@,
so if @i=0@, we would expect @s@ to be @0@. Our invariant is clearly an overapproximation
of the reachable space, and SBV is telling us that we need to constrain and outlaw
the state @{n = 0, i = 0, s = 1}@. Clearly, the invariant has to state something
about the relationship between @i@ and @s@, which we are missing in this case.

== Failing to maintain the invariant

What happens if we pose an invariant that the loop actually does not maintain? Here
is an example:

>>> let invariant SumS{n, i, s} = s .<= i .&& s .== (i*(i+1)) `sDiv` 2 .&& i .<= n
>>> void $ correctness invariant Nothing
Following proof obligation failed:
==================================
  Invariant for loop "i < n" is not maintained by the body:
    Before: SumS {n = 3, i = 1, s = 1}
    After : SumS {n = 3, i = 2, s = 3}

Here, we posed the extra incorrect invariant that @s <= i@ must be maintained, and SBV found us a reachable state that violates the invariant. The
/before/ state indeed satisfies @s <= i@, but the /after/ state does not. Note that the proof fails in this case not because the program
is incorrect, but the stipulated invariant is not valid.

== Having a bad measure, Part I

The termination measure must always be non-negative:

>>> let invariant SumS{n, i, s} = s .== (i*(i+1)) `sDiv` 2 .&& i .<= n
>>> let measure   SumS{n, i}    = [1-i]
>>> void $ correctness invariant (Just measure)
Following proof obligation failed:
==================================
  Measure for loop "i < n" is negative:
    State  : SumS {n = 3, i = 2, s = 3}
    Measure: -1

The failure is pretty obvious in this case: Measure produces a negative value.

== Having a bad measure, Part II

The other way we can have a bad measure is if it fails to decrease through the loop body:

>>> let invariant SumS{n, i, s} = s .== (i*(i+1)) `sDiv` 2 .&& i .<= n
>>> let measure   SumS{n, i}    = [n + i]
>>> void $ correctness invariant (Just measure)
Following proof obligations failed:
===================================
  Measure for loop "i < n" is negative:
    State  : SumS {n = 0, i = -1, s = 0}
    Measure: -1
  Measure for loop "i < n" does not decrease:
    Before : SumS {n = 0, i = -1, s = 0}
    Measure: -1
    After  : SumS {n = 0, i = 0, s = 0}
    Measure: 0

Clearly, as @i@ increases, so does our bogus measure @n+i@. Note that in this case the counterexample has
@i@ as a negative value, as the SMT solver finds a counter-example to induction, not
necessarily a reachable state. Obviously, all such failures need to be addressed for the full proof.
-}
