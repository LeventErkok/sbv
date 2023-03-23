-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.WeakestPreconditions.Fib
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proof of correctness of an imperative fibonacci algorithm, using weakest
-- preconditions. Note that due to the recursive nature of fibonacci, we
-- cannot write the spec directly, so we use an uninterpreted function
-- and proper axioms to complete the proof.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.WeakestPreconditions.Fib where

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

-- | The state for the sum program, parameterized over a base type @a@.
data FibS a = FibS { n :: a    -- ^ The input value
                   , i :: a    -- ^ Loop counter
                   , k :: a    -- ^ tracks @fib (i+1)@
                   , m :: a    -- ^ tracks @fib i@
                   }
                   deriving (Show, Generic, Mergeable, Functor, Foldable, Traversable)

-- | Show instance for 'FibS'. The above deriving clause would work just as well,
-- but we want it to be a little prettier here, and hence the @OVERLAPS@ directive.
instance {-# OVERLAPS #-} (SymVal a, Show a) => Show (FibS (SBV a)) where
   show (FibS n i k m) = "{n = " ++ sh n ++ ", i = " ++ sh i ++ ", k = " ++ sh k ++ ", m = " ++ sh m ++ "}"
     where sh v = maybe "<symbolic>" show (unliteral v)

-- | 'Fresh' instance for the program state
instance SymVal a => Fresh IO (FibS (SBV a)) where
  fresh = FibS <$> freshVar_  <*> freshVar_  <*> freshVar_ <*> freshVar_

-- | Helper type synonym
type F = FibS SInteger

-- * The algorithm

-- | The imperative fibonacci algorithm:
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
-- When the loop terminates, @m@ contains @fib(n)@.
algorithm :: Stmt F
algorithm = Seq [ Assign $ \st -> st{i = 0, k = 1, m = 0}
                , assert "n >= 0" $ \FibS{n} -> n .>= 0
                , While "i < n"
                        (\FibS{n, i, k, m} -> i .<= n .&& k .== fib (i+1) .&& m .== fib i)
                        (Just (\FibS{n, i} -> [n-i]))
                        (\FibS{n, i} -> i .< n)
                        $ Seq [ Assign $ \st@FibS{m, k} -> st{m = k, k = m + k}
                              , Assign $ \st@FibS{i}    -> st{i = i+1}
                              ]
                ]

-- | Symbolic fibonacci as our specification. Note that we cannot
-- really implement the fibonacci function since it is not
-- symbolically terminating.  So, we instead uninterpret and
-- axiomatize it below.
--
-- NB. The concrete part of the definition is only used in calls to 'traceExecution'
-- and is not needed for the proof. If you don't need to call 'traceExecution', you
-- can simply ignore that part and directly uninterpret.
fib :: SInteger -> SInteger
fib x
 | isSymbolic x = uninterpret "fib" x
 | True         = go x
 where go i = ite (i .== 0) 0
            $ ite (i .== 1) 1
            $ go (i-1) + go (i-2)

-- | Constraints and axioms we need to state explicitly to tell
-- the SMT solver about our specification for fibonacci.
axiomatizeFib :: Symbolic ()
axiomatizeFib = do -- Base cases.
                   -- Note that we write these in forms of implications,
                   -- instead of the more direct:
                   --
                   --    constrain $ fib 0 .== 0
                   --    constrain $ fib 1 .== 1
                   --
                   -- As otherwise they would be concretely evaluated and
                   -- would not be sent to the SMT solver!
                   x <- sInteger_
                   constrain $ x .== 0 .=> fib x .== 0
                   constrain $ x .== 1 .=> fib x .== 1

                   constrain $ \(Forall n) -> fib (n+2) .== fib (n+1) + fib n

-- | Precondition for our program: @n@ must be non-negative.
pre :: F -> SBool
pre FibS{n} = n .>= 0

-- | Postcondition for our program: @m = fib n@
post :: F -> SBool
post FibS{n, m} = m .== fib n

-- | Stability condition: Program must leave @n@ unchanged.
noChange :: Stable F
noChange = [stable "n" n]

-- | A program is the algorithm, together with its pre- and post-conditions.
imperativeFib :: Program F
imperativeFib = Program { setup         = axiomatizeFib
                        , precondition  = pre
                        , program       = algorithm
                        , postcondition = post
                        , stability     = noChange
                        }

-- * Correctness

-- | With the axioms in place, it is trivial to establish correctness:
--
-- >>> correctness
-- Total correctness is established.
-- Q.E.D.
--
-- Note that I found this proof to be quite fragile: If you do not get the algorithm right
-- or the axioms aren't in place, z3 simply goes to an infinite loop, instead of providing
-- counter-examples. Of course, this is to be expected with the quantifiers present.
correctness :: IO (ProofResult (FibS Integer))
correctness = wpProveWith defaultWPCfg{wpVerbose=True} imperativeFib

-- * Concrete execution
-- $concreteExec

{- $concreteExec

Example concrete run. As we mentioned in the definition for 'fib', the concrete-execution
function cannot deal with uninterpreted functions and axioms for obvious reasons. In those
cases we revert to the concrete definition. Here's an example run:

>>> traceExecution imperativeFib $ FibS {n = 3, i = 0, k = 0, m = 0}
*** Precondition holds, starting execution:
  {n = 3, i = 0, k = 0, m = 0}
===> [1.1] Assign
  {n = 3, i = 0, k = 1, m = 0}
===> [1.2] Conditional, taking the "then" branch
  {n = 3, i = 0, k = 1, m = 0}
===> [1.2.1] Skip
  {n = 3, i = 0, k = 1, m = 0}
===> [1.3] Loop "i < n": condition holds, executing the body
  {n = 3, i = 0, k = 1, m = 0}
===> [1.3.{1}.1] Assign
  {n = 3, i = 0, k = 1, m = 1}
===> [1.3.{1}.2] Assign
  {n = 3, i = 1, k = 1, m = 1}
===> [1.3] Loop "i < n": condition holds, executing the body
  {n = 3, i = 1, k = 1, m = 1}
===> [1.3.{2}.1] Assign
  {n = 3, i = 1, k = 2, m = 1}
===> [1.3.{2}.2] Assign
  {n = 3, i = 2, k = 2, m = 1}
===> [1.3] Loop "i < n": condition holds, executing the body
  {n = 3, i = 2, k = 2, m = 1}
===> [1.3.{3}.1] Assign
  {n = 3, i = 2, k = 3, m = 2}
===> [1.3.{3}.2] Assign
  {n = 3, i = 3, k = 3, m = 2}
===> [1.3] Loop "i < n": condition fails, terminating
  {n = 3, i = 3, k = 3, m = 2}
*** Program successfully terminated, post condition holds of the final state:
  {n = 3, i = 3, k = 3, m = 2}
Program terminated successfully. Final state:
  {n = 3, i = 3, k = 3, m = 2}

As expected, @fib 3@ is @2@.
-}
