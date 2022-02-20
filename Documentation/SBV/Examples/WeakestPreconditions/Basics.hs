-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.WeakestPreconditions.Basics
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Some basic aspects of weakest preconditions, demonstrating programs
-- that do not use while loops. We use a simple increment program as
-- an example.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.WeakestPreconditions.Basics where

import Data.SBV
import Data.SBV.Control

import Data.SBV.Tools.WeakestPreconditions

import GHC.Generics (Generic)

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV
-- >>> import Data.SBV.Control
-- >>> import Data.SBV.Tools.WeakestPreconditions

-- * Program state

-- | The state for the swap program, parameterized over a base type @a@.
data IncS a = IncS { x :: a    -- ^ Input value
                   , y :: a    -- ^ Output
                   }
                   deriving (Show, Generic, Mergeable, Functor, Foldable, Traversable)

-- | Show instance for 'IncS'. The above deriving clause would work just as well,
-- but we want it to be a little prettier here, and hence the @OVERLAPS@ directive.
instance {-# OVERLAPS #-} (SymVal a, Show a) => Show (IncS (SBV a)) where
   show (IncS x y) = "{x = " ++ sh x ++ ", y = " ++ sh y ++ "}"
     where sh v = maybe "<symbolic>" show (unliteral v)

-- | 'Fresh' instance for the program state
instance SymVal a => Fresh IO (IncS (SBV a)) where
  fresh = IncS <$> freshVar_  <*> freshVar_

-- | Helper type synonym
type I = IncS SInteger

-- * The algorithm

-- | The increment algorithm:
--
-- @
--    y = x+1
-- @
--
-- The point here isn't really that this program is interesting, but we want to
-- demonstrate various aspects of WP proofs. So, we take a before and after
-- program to annotate our algorithm so we can experiment later.
algorithm :: Stmt I -> Stmt I -> Stmt I
algorithm before after = Seq [ before
                             , Assign $ \st@IncS{x} -> st{y = x+1}
                             , after
                             ]

-- | Precondition for our program. Strictly speaking, we don't really need any preconditions,
-- but for example purposes, we'll require @x@ to be non-negative.
pre :: I -> SBool
pre IncS{x} = x .>= 0

-- | Postcondition for our program: @y@ must equal @x+1@.
post :: I -> SBool
post IncS{x, y} = y .== x+1

-- | Stability: @x@ must remain unchanged.
noChange :: Stable I
noChange = [stable "x" x]

-- | A program is the algorithm, together with its pre- and post-conditions.
imperativeInc :: Stmt I -> Stmt I -> Program I
imperativeInc before after = Program { setup         = return ()
                                     , precondition  = pre
                                     , program       = algorithm before after
                                     , postcondition = post
                                     , stability     = noChange
                                     }

-- * Correctness

-- | State the correctness with respect to before/after programs. In the simple
-- case of nothing prior/after, we have the obvious proof:
--
-- >>> correctness Skip Skip
-- Total correctness is established.
-- Q.E.D.
correctness :: Stmt I -> Stmt I -> IO (ProofResult (IncS Integer))
correctness before after = wpProveWith defaultWPCfg{wpVerbose=True} (imperativeInc before after)

-- * Example proof attempts
--
-- $examples

{- $examples
It is instructive to look at how the proof changes as we put in different @pre@ and @post@ values.

== Violating the post condition

If we stick in an extra increment for @y@ after, we can easily break the postcondition:

>>> :set -XNamedFieldPuns
>>> import Control.Monad (void)
>>> void $ correctness Skip $ Assign $ \st@IncS{y} -> st{y = y+1}
Following proof obligation failed:
==================================
  Postcondition fails:
    Start: IncS {x = 0, y = 0}
    End  : IncS {x = 0, y = 2}

We're told that the program ends up in a state where @x=0@ and @y=2@, violating the requirement @y=x+1@, as expected.

== Using 'assert'

There are two main use cases for 'assert', which merely ends up being a call to 'Abort'.
One is making sure the inputs are well formed. And the other is the user putting in their
own invariants into the code.

Let's assume that we only want to accept strictly positive values of @x@. We can try:

>>> void $ correctness (assert "x > 0" (\st@IncS{x} -> x .> 0)) Skip
Following proof obligation failed:
==================================
  Abort "x > 0" condition is satisfiable:
    Before: IncS {x = 0, y = 0}
    After : IncS {x = 0, y = 0}

Recall that our precondition ('pre') required @x@ to be non-negative. So, we can put in something weaker and it would be fine:

>>> void $ correctness (assert "x > -5" (\st@IncS{x} -> x .> -5)) Skip
Total correctness is established.

In this case the precondition to our program ensures that the 'assert' will always be satisfied.

As another example, let us put a post assertion that @y@ is even:

>>> void $ correctness Skip (assert "y is even" (\st@IncS{y} -> y `sMod` 2 .== 0))
Following proof obligation failed:
==================================
  Abort "y is even" condition is satisfiable:
    Before: IncS {x = 0, y = 0}
    After : IncS {x = 0, y = 1}

It is important to emphasize that you can put whatever invariant you might want:

>>> void $ correctness Skip (assert "y > x" (\st@IncS{x, y} -> y .> x))
Total correctness is established.

== Violating stability

What happens if our program modifies @x@? After all, we can simply set @x=10@ and @y=11@ and our post condition would be satisfied:

>>> void $ correctness Skip (Assign $ \st -> st{x = 10, y = 11})
Following proof obligation failed:
==================================
  Stability fails for "x":
    Before: IncS {x = 0, y = 1}
    After : IncS {x = 10, y = 11}

So, the stability condition prevents programs from cheating!
-}
