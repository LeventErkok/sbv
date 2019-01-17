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

-- For doctest use only
--
-- $setup
-- >>> :set -XNamedFieldPuns

-- * System state

-- | The state for the sum program, parameterized over a base type @a@.
data SumS a = SumS { i :: a    -- ^ Loop counter
                   , s :: a    -- ^ Running sum
                   , n :: a    -- ^ The input value
                   }

-- | Show instance for 'SumS'. A deriving clause would work just as well,
-- but we want it to be a little prettier here.
instance (SymVal a, Show a) => Show (SumS (SBV a)) where
   show (SumS i s n) = "{n = " ++ sh n ++ ", i = " ++ sh i ++ ", s = " ++ sh s ++ "}"
     where sh v = case unliteral v of
                    Nothing -> "<symbolic>"
                    Just l  -> show l

-- | Make our state 'Data.SBV.Control.Queariable'
instance (SymVal a, SMTValue a) => Queriable IO (SumS (SBV a)) (SumS a) where
 create                = SumS <$> freshVar_  <*> freshVar_  <*> freshVar_
 project SumS{i, s, n} = SumS <$> getValue i <*> getValue s <*> getValue n
 embed   SumS{i, s, n} = return $ SumS (literal i) (literal s) (literal n)

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
imperativeSum :: Invariant S -> Measure S -> Program S
imperativeSum invariant measure =
        Seq [ Assign $ \st -> st{i = 0, s = 0}
            , While "i <= n"
                    invariant
                    measure
                    (\SumS{i, n} -> i .<= n)
                    $ Seq [ Assign $ \st@SumS{i, s} -> st{s = s+i}
                          , Assign $ \st@SumS{i}    -> st{i = i+1}
                          ]
            ]

-- * Weakest precondition proofs

-- | Check that the program terminates and @s@ equals @n*(n+1)/2@
-- upon termination, i.e., the sum of all numbers upto @n@. Note
-- that this only holds if @n >= 0@ to start with, so our
-- as stipulated by our correctness predicate in the program.
--
-- The correct termination measure is @n-i@: It goes down in each
-- iteration provided we start with @n >= 0@ and it always remains
-- non-negative while the loop is executing.
--
-- The correct invariant is a conjunct. First, we have that @s@ is
-- equivalent to the sum of numbers @0@ upto but not including @i@.
-- (When @i=0@, we define this sum to be @0@.) This clearly holds at
-- the beginning when @i = s = 0@, and is maintained in each iteration
-- of the body. Second, it always holds that @i <= n+1@ as long as the
-- loop executes, both before and after each execution of the body.
correctness :: Invariant S -> Measure S -> IO (ProofResult (SumS Integer))
correctness invariant measure = checkWith z3{verbose=False} True (imperativeSum invariant measure) prop
  where prop SumS{s, n} = n .>= 0 .=> s .== (n * (n+1)) `sDiv` 2


-- inv1 _             = sFalse
-- inv2 _             = sTrue
-- inv3 SumS{i, n}    = n .>= 0 .=> i .<= n+1
-- inv4 SumS{i, s, n} = n .>= 0 .=> s .== (i * (i-1)) `sDiv` 2
-- inv5 s@SumS{n}     = n .>= 0 .=> inv3 s .&& inv4 s
-- measure1 SumS{i} = i - 10
-- measure2 SumS{i} = i
-- measure3 SumS{n, i} = n-i

-- * Example cases

{- $examples

== Always false invariant

The simplest thing to try is to see what happens if the invariant
is always false:

>>> let invariant _          = sFalse
>>> let measure   SumS{i, n} = n - i
>>> correctness invariant measure
Following proof obligation failed:
===================================
  Loop "i <= n": Invariant must hold prior to loop entry
<BLANKLINE>
Execution leading to failed proof obligation:
=============================================
  {n = 0, i = 0, s = 0}
===> [1.1] Assign
  {n = 0, i = 0, s = 0}
===> [1.2] Loop i <= n: invariant fails to hold prior to loop entry
<BLANKLINE>
Program execution aborted in state:
  {n = 0, i = 0, s = 0}

When the invariant is constant false, it fails upon entry to the loop, and thus the
proof itself fails.

== Full proof

>>> let invariant SumS{i, s, n} = n .>= 0 .=> s .== (i*(i-1)) `sDiv` 2 .&& i .<= n+1
>>> let measure   SumS{i, n}    = n - i
>>> correctness invariant measure
Total correctness is established.

Finally, we have the full proof and a guarantee of termination!
-}
