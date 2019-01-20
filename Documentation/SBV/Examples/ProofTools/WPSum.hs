-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.ProofTools.WPSum
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proof of correctness of an imperative summation algorithm, using weakest
-- preconditions. We investigate a few different invariants and see how
-- different versions lead to proofs and failures.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}

module Documentation.SBV.Examples.ProofTools.WPSum where

import Data.SBV
import Data.SBV.Control

import Data.SBV.Tools.WeakestPreconditions

-- * System state

-- | The state for the sum program, parameterized over a base type @a@.
data SumS a = SumS { n :: a    -- ^ The input value
                   , i :: a    -- ^ Loop counter
                   , s :: a    -- ^ Running sum
                   }
                   deriving Show

-- | Show instance for 'SumS'. The above deriving clause would work just as well,
-- but we want it to be a little prettier here, and hence the @OVERLAPS@ directive.
instance {-# OVERLAPS #-} (SymVal a, Show a) => Show (SumS (SBV a)) where
   show (SumS n i s) = "{n = " ++ sh n ++ ", i = " ++ sh i ++ ", s = " ++ sh s ++ "}"
     where sh v = case unliteral v of
                    Nothing -> "<symbolic>"
                    Just l  -> show l

-- | Make our state 'Data.SBV.Control.Queariable'
instance (SymVal a, SMTValue a) => Queriable IO (SumS (SBV a)) (SumS a) where
 create                = SumS <$> freshVar_  <*> freshVar_  <*> freshVar_
 project SumS{n, i, s} = SumS <$> getValue n <*> getValue i <*> getValue s
 embed   SumS{n, i, s} = return $ SumS (literal n) (literal i) (literal s)

-- | We also need it mergeable:
instance Mergeable a => Mergeable (SumS a) where
  symbolicMerge force c SumS{n = n1, i = i1, s = s1} SumS{n = n2, i = i2, s = s2}
        = SumS { n = symbolicMerge force c n1 n2
               , i = symbolicMerge force c i1 i2
               , s = symbolicMerge force c s1 s2
               }

-- | Helper type synonym
type S = SumS SInteger

-- * The algorithm

-- | The imperative summation algorithm:
--
-- @
--    i = 0
--    s = 0
--    while i <= n
--      s = s+i
--      i = i+1
-- @
--
-- Note that we need to explicitly annotate each loop with its invariant and the termination
-- measure. For convenience, we take those two as parameters, so we can experiment later.
algorithm :: Invariant S -> Measure S -> Stmt S
algorithm inv msr = Seq [ Assign $ \st -> st{i = 0, s = 0}
                        , While "i <= n"
                                inv
                                msr
                                (\SumS{i, n} -> i .<= n)
                                $ Seq [ Assign $ \st@SumS{i, s} -> st{s = s+i}
                                      , Assign $ \st@SumS{i}    -> st{i = i+1}
                                      ]
                        ]

-- | Precondition for our program: @n@ must be non-negative.
pre :: S -> SBool
pre SumS{n} = n .>= 0

-- | Postcondition for our program: @s@ must be the sum of all numbers up to
-- and including @n@.
post :: S -> SBool
post SumS{n, s} = s .== (n * (n+1)) `sDiv` 2

-- | A program is the algorithm, together with its pre- and post-conditions.
imperativeSum :: Invariant S -> Measure S -> Program S
imperativeSum inv msr = Program { precondition  = pre
                                , program       = algorithm inv msr
                                , postcondition = post
                                }

-- * Correctness

-- | Check that the program terminates and @s@ equals @n*(n+1)/2@
-- upon termination, i.e., the sum of all numbers upto @n@. Note
-- that this only holds if @n >= 0@ to start with, as guaranteed
-- by the precondition of our program.
--
-- The correct termination measure is @n-i@: It goes down in each
-- iteration provided we start with @n >= 0@ and it always remains
-- non-negative while the loop is executing.
--
-- The correct invariant is a conjunction of two facts. First, @s@ is
-- equivalent to the sum of numbers @0@ upto but not including @i@.
-- (When @i=0@, we define this sum to be @0@.) This clearly holds at
-- the beginning when @i = s = 0@, and is maintained in each iteration
-- of the body. Second, it always holds that @i <= n+1@ as long as the
-- loop executes, both before and after each execution of the body.
-- When the loop terminates, it holds that @i = n+1@. Since the invariant says
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
-- >>> let invariant SumS{n, i, s} = s .== (i*(i-1)) `sDiv` 2 .&& i .<= n+1
-- >>> let measure   SumS{n, i}    = n - i
-- >>> correctness invariant measure
-- Total correctness is established.
-- Q.E.D.
correctness :: Invariant S -> Measure S -> IO ()
correctness inv msr = print =<< checkWith z3{verbose=False} True (imperativeSum inv msr)

-- * Example proof attempts
--
-- $examples

{- $examples
It is instructive to look at several proof attempts to see what can go wrong and how
the weakest-precondition engine behaves.

== Always false invariant

Let's see what happens if we have an always false invariant. Clearly, this will not
do the job, but it is instructive to see the output:

>>> :set -XNamedFieldPuns
>>> let invariant _          = sFalse
>>> let measure   SumS{n, i} = n - i
>>> correctness invariant measure
Following proof obligation failed:
===================================
  Loop "i <= n": Invariant must hold prior to loop entry
<BLANKLINE>
Execution trace:
================
  {n = 0, i = 0, s = 0}
===> Precondition holds, starting execution
  {n = 0, i = 0, s = 0}
===> [1.1] Assign
  {n = 0, i = 0, s = 0}
===> [1.2] Loop i <= n: invariant fails to hold prior to loop entry
<BLANKLINE>
Analysis complete. Proof Failed.
Proof failure: Loop i <= n: invariant fails to hold prior to loop entry
Starting state:
  SumS {n = 0, i = 0, s = 0}
Failed in state:
  SumS {n = 0, i = 0, s = 0}

When the invariant is constant false, it fails upon entry to the loop, and thus the
proof itself fails.

== Always true invariant

The invariant must hold prior to entry to the loop, after the loop-body
executes, and must be strong enough to establish the postcondition. The easiest
thing to try would be the invariant that always returns true:

>>> :set -XNamedFieldPuns
>>> let invariant _          = sTrue
>>> let measure   SumS{n, i} = n - i
>>> correctness invariant measure
Following proof obligation failed:
===================================
  Loop "i <= n": Invariant must establish the post condition
<BLANKLINE>
No violating trace found (searched up to depth: 20)
Indeterminate: Not all proof obligations were established.

In this case, we are told that the invariant was not sufficient to establish
the postcondition, as expected. Also note that we do not get a violation trace,
because there is none! No execution of this program will violate any of the
requirements. It just happens that the invariant isn't strong enough to establish
the required property. (Note that SBV might fail to provide a counter-example
trace if it is beyond depth 20, as indicated in the message.)

== Failing to maintain the invariant

What happens if we pose an invariant that the loop actually does not maintain? Here
is an example:

>>> :set -XNamedFieldPuns
>>> let invariant SumS{n, i, s} = s .== i .&& s .== (i*(i-1)) `sDiv` 2 .&& i .<= n+1
>>> let measure   SumS{n, i}    = n - i
>>> correctness invariant measure
Following proof obligation failed:
===================================
  Loop "i <= n": Invariant must be maintained by the loop
<BLANKLINE>
  {n = 1, i = 0, s = 0}
===> Precondition holds, starting execution
  {n = 1, i = 0, s = 0}
===> [1.1] Assign
  {n = 1, i = 0, s = 0}
===> [1.2] Loop i <= n: condition holds, executing the body
  {n = 1, i = 0, s = 0}
===> [1.2.{1}.1] Assign
  {n = 1, i = 0, s = 0}
===> [1.2.{1}.2] Assign
  {n = 1, i = 1, s = 0}
===> [1.2] Loop i <= n: invariant fails to hold in iteration 2
Proof failure: Not all proof obligations were established.
Starting state:
  SumS {n = 1, i = 0, s = 0}
Failed in state:
  SumS {n = 1, i = 2, s = 1}

Here, we posed the extra incorrect invariant that @s@ must equal @i@, and SBV found us a trace that violates the invariant. Note that
the proof fails in this case not because the program is incorrect, but the stipulated invariant is not valid.
-}
