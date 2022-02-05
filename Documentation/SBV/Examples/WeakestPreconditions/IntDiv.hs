-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.WeakestPreconditions.IntDiv
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proof of correctness of an imperative integer division algorithm, using
-- weakest preconditions. The algorithm simply keeps subtracting the divisor
-- until the desired quotient and the remainder is found.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.WeakestPreconditions.IntDiv where

import Data.SBV
import Data.SBV.Control

import Data.SBV.Tools.WeakestPreconditions

import GHC.Generics (Generic)

-- * Program state

-- | The state for the division program, parameterized over a base type @a@.
data DivS a = DivS { x :: a   -- ^ The dividend
                   , y :: a   -- ^ The divisor
                   , q :: a   -- ^ The quotient
                   , r :: a   -- ^ The remainder
                   }
                   deriving (Show, Generic, Mergeable, Functor, Foldable, Traversable)

-- | Show instance for 'DivS'. The above deriving clause would work just as well,
-- but we want it to be a little prettier here, and hence the @OVERLAPS@ directive.
instance {-# OVERLAPS #-} (SymVal a, Show a) => Show (DivS (SBV a)) where
   show (DivS x y q r) = "{x = " ++ sh x ++ ", y = " ++ sh y ++ ", q = " ++ sh q ++ ", r = " ++ sh r ++ "}"
     where sh v = maybe "<symbolic>" show (unliteral v)

-- | 'Fresh' instance for the program state
instance SymVal a => Fresh IO (DivS (SBV a)) where
  fresh = DivS <$> freshVar_  <*> freshVar_ <*> freshVar_ <*> freshVar_

-- | Helper type synonym
type D = DivS SInteger

-- * The algorithm

-- | The imperative division algorithm, assuming non-negative @x@ and strictly positive @y@:
--
-- @
--    r = x                     -- set remainder to x
--    q = 0                     -- set quotient  to 0
--    while y <= r              -- while we can still subtract
--      r = r - y                    -- reduce the remainder
--      q = q + 1                    -- increase the quotient
-- @
--
-- Note that we need to explicitly annotate each loop with its invariant and the termination
-- measure. For convenience, we take those two as parameters for simplicity.
algorithm :: Invariant D -> Maybe (Measure D) -> Stmt D
algorithm inv msr = Seq [ assert "x, y >= 0" $ \DivS{x, y} -> x .>= 0 .&& y .>= 0
                        , Assign $ \st@DivS{x} -> st{r = x, q = 0}
                        , While "y <= r"
                                inv
                                msr
                                (\DivS{y, r} -> y .<= r)
                                $ Assign $ \st@DivS{y, q, r} -> st{r = r - y, q = q + 1}
                        ]

-- | Precondition for our program: @x@ must non-negative and @y@ must be strictly positive.
-- Note that there is an explicit call to 'Data.SBV.Tools.WeakestPreconditions.abort' in our program to protect against this case, so
-- if we do not have this precondition, all programs will fail.
pre :: D -> SBool
pre DivS{x, y} = x .>= 0 .&& y .> 0

-- | Postcondition for our program: Remainder must be non-negative and less than @y@,
-- and it must hold that @x = q*y + r@:
post :: D -> SBool
post DivS{x, y, q, r} = r .>= 0 .&& r .< y .&& x .== q * y + r

-- | Stability: @x@ and @y@ must remain unchanged.
noChange :: Stable D
noChange = [stable "x" x, stable "y" y]

-- | A program is the algorithm, together with its pre- and post-conditions.
imperativeDiv :: Invariant D -> Maybe (Measure D) -> Program D
imperativeDiv inv msr = Program { setup         = return ()
                                , precondition  = pre
                                , program       = algorithm inv msr
                                , postcondition = post
                                , stability     = noChange
                                }

-- * Correctness

-- | The invariant is simply that @x = q * y + r@ holds at all times and @r@ is strictly positive.
-- We need the @y > 0@ part of the invariant to establish the measure decreases, which is guaranteed
-- by our precondition.
invariant :: Invariant D
invariant DivS{x, y, q, r} = y .> 0 .&& r .>= 0 .&& x .== q * y + r

-- | The measure. In each iteration @r@ decreases, but always remains positive.
-- Since @y@ is strictly positive, @r@ can serve as a measure for the loop.
measure :: Measure D
measure DivS{r} = [r]

-- | Check that the program terminates and the post condition holds. We have:
--
-- >>> correctness
-- Total correctness is established.
-- Q.E.D.
correctness :: IO ()
correctness = print =<< wpProveWith defaultWPCfg{wpVerbose=True} (imperativeDiv invariant (Just measure))
