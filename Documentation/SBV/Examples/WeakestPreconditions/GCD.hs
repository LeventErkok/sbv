-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.WeakestPreconditions.GCD
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proof of correctness of an imperative GCD (greatest-common divisor)
-- algorithm, using weakest preconditions. The termination measure here
-- illustrates the use of lexicographic ordering. Also, since symbolic
-- version of GCD is not symbolically terminating, this is another
-- example of using uninterpreted functions and axioms as one writes
-- specifications for WP proofs.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.WeakestPreconditions.GCD where

import Data.SBV
import Data.SBV.Control

import Data.SBV.Tools.WeakestPreconditions

import GHC.Generics (Generic)

-- Access Prelude's gcd, but qualified:
import Prelude hiding (gcd)
import qualified Prelude as P (gcd)

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV
-- >>> import Data.SBV.Control
-- >>> import Data.SBV.Tools.WeakestPreconditions

-- * Program state

-- | The state for the sum program, parameterized over a base type @a@.
data GCDS a = GCDS { x :: a    -- ^ First value
                   , y :: a    -- ^ Second value
                   , i :: a    -- ^ Copy of x to be modified
                   , j :: a    -- ^ Copy of y to be modified
                   }
                   deriving (Show, Generic, Mergeable, Functor, Foldable, Traversable)

-- | Show instance for 'GCDS'. The above deriving clause would work just as well,
-- but we want it to be a little prettier here, and hence the @OVERLAPS@ directive.
instance {-# OVERLAPS #-} (SymVal a, Show a) => Show (GCDS (SBV a)) where
   show (GCDS x y i j) = "{x = " ++ sh x ++ ", y = " ++ sh y ++ ", i = " ++ sh i ++ ", j = " ++ sh j ++ "}"
     where sh v = maybe "<symbolic>" show (unliteral v)

-- | 'Fresh' instance for the program state
instance SymVal a => Fresh IO (GCDS (SBV a)) where
  fresh = GCDS <$> freshVar_  <*> freshVar_  <*> freshVar_ <*> freshVar_

-- | Helper type synonym
type G = GCDS SInteger

-- * The algorithm

-- | The imperative GCD algorithm, assuming strictly positive @x@ and @y@:
--
-- @
--    i = x
--    j = y
--    while i != j      -- While not equal
--      if i > j
--         i = i - j    -- i is greater; reduce it by j
--      else
--         j = j - i    -- j is greater; reduce it by i
-- @
--
-- When the loop terminates, @i@ equals @j@ and contains @GCD(x, y)@.
algorithm :: Stmt G
algorithm = Seq [ assert "x > 0, y > 0" $ \GCDS{x, y} -> x .> 0 .&& y .> 0
                , Assign $ \st@GCDS{x, y} -> st{i = x, j = y}
                , While "i != j"
                        inv
                        (Just msr)
                        (\GCDS{i, j} -> i ./= j)
                        $ If (\GCDS{i, j} -> i .> j)
                             (Assign $ \st@GCDS{i, j} -> st{i = i - j})
                             (Assign $ \st@GCDS{i, j} -> st{j = j - i})
                ]
  where -- This invariant simply states that the value of the gcd remains the same
        -- through the iterations.
        inv GCDS{x, y, i, j} = x .> 0 .&& y .> 0 .&& i .> 0 .&& j .> 0 .&& gcd x y .== gcd i j

        -- The measure can be taken as @i+j@ going down. However, we
        -- can be more explicit and use the lexicographic nature: Notice
        -- that in each iteration either @i@ goes down, or it stays the same
        -- and @j@ goes down; and they never go below @0@. So we can
        -- have the pair and use the lexicographic ordering.
        msr GCDS{i, j} = [i, j]

-- | Symbolic GCD as our specification. Note that we cannot
-- really implement the GCD function since it is not
-- symbolically terminating.  So, we instead uninterpret and
-- axiomatize it below.
--
-- NB. The concrete part of the definition is only used in calls to 'traceExecution'
-- and is not needed for the proof. If you don't need to call 'traceExecution', you
-- can simply ignore that part and directly uninterpret. In that case, we simply
-- use Prelude's version.
gcd :: SInteger -> SInteger -> SInteger
gcd x y
 | Just i <- unliteral x, Just j <- unliteral y
 = literal (P.gcd i j)
 | True
 = uninterpret "gcd" x y

-- | Constraints and axioms we need to state explicitly to tell
-- the SMT solver about our specification for GCD.
axiomatizeGCD :: Symbolic ()
axiomatizeGCD = do constrain $ \(Forall x)            -> x .> 0            .=> gcd x x     .== x
                   constrain $ \(Forall x) (Forall y) -> x .> 0 .&& y .> 0 .=> gcd (x+y) y .== gcd x y
                   constrain $ \(Forall x) (Forall y) -> x .> 0 .&& y .> 0 .=> gcd x (y+x) .== gcd x y

-- | Precondition for our program: @x@ and @y@ must be strictly positive
pre :: G -> SBool
pre GCDS{x, y} = x .> 0 .&& y .> 0

-- | Postcondition for our program: @i == j@ and @i = gcd x y@
post :: G -> SBool
post GCDS{x, y, i, j} = i .== j .&& i .== gcd x y

-- | Stability condition: Program must leave @x@ and @y@ unchanged.
noChange :: Stable G
noChange = [stable "x" x, stable "y" y]

-- | A program is the algorithm, together with its pre- and post-conditions.
imperativeGCD :: Program G
imperativeGCD = Program { setup         = axiomatizeGCD
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
correctness :: IO (ProofResult (GCDS Integer))
correctness = wpProveWith defaultWPCfg{wpVerbose=True} imperativeGCD

-- * Concrete execution
-- $concreteExec

{- $concreteExec

Example concrete run. As we mentioned in the definition for 'gcd', the concrete-execution
function cannot deal with uninterpreted functions and axioms for obvious reasons. In those
cases we revert to the concrete definition. Here's an example run:

>>> traceExecution imperativeGCD $ GCDS {x = 14, y = 4, i = 0, j = 0}
*** Precondition holds, starting execution:
  {x = 14, y = 4, i = 0, j = 0}
===> [1.1] Conditional, taking the "then" branch
  {x = 14, y = 4, i = 0, j = 0}
===> [1.1.1] Skip
  {x = 14, y = 4, i = 0, j = 0}
===> [1.2] Assign
  {x = 14, y = 4, i = 14, j = 4}
===> [1.3] Loop "i != j": condition holds, executing the body
  {x = 14, y = 4, i = 14, j = 4}
===> [1.3.{1}] Conditional, taking the "then" branch
  {x = 14, y = 4, i = 14, j = 4}
===> [1.3.{1}.1] Assign
  {x = 14, y = 4, i = 10, j = 4}
===> [1.3] Loop "i != j": condition holds, executing the body
  {x = 14, y = 4, i = 10, j = 4}
===> [1.3.{2}] Conditional, taking the "then" branch
  {x = 14, y = 4, i = 10, j = 4}
===> [1.3.{2}.1] Assign
  {x = 14, y = 4, i = 6, j = 4}
===> [1.3] Loop "i != j": condition holds, executing the body
  {x = 14, y = 4, i = 6, j = 4}
===> [1.3.{3}] Conditional, taking the "then" branch
  {x = 14, y = 4, i = 6, j = 4}
===> [1.3.{3}.1] Assign
  {x = 14, y = 4, i = 2, j = 4}
===> [1.3] Loop "i != j": condition holds, executing the body
  {x = 14, y = 4, i = 2, j = 4}
===> [1.3.{4}] Conditional, taking the "else" branch
  {x = 14, y = 4, i = 2, j = 4}
===> [1.3.{4}.2] Assign
  {x = 14, y = 4, i = 2, j = 2}
===> [1.3] Loop "i != j": condition fails, terminating
  {x = 14, y = 4, i = 2, j = 2}
*** Program successfully terminated, post condition holds of the final state:
  {x = 14, y = 4, i = 2, j = 2}
Program terminated successfully. Final state:
  {x = 14, y = 4, i = 2, j = 2}

As expected, @gcd 14 4@ is @2@.
-}
