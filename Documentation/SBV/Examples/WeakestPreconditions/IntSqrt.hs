-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.WeakestPreconditions.IntSqrt
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proof of correctness of an imperative integer square-root algorithm, using
-- weakest preconditions. The algorithm computes the floor of the square-root
-- of a given non-negative integer by keeping a running some of all odd numbers
-- starting from 1. Recall that @1+3+5+...+(2n+1) = (n+1)^2@, thus we can
-- stop the counting when we exceed the input number.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.WeakestPreconditions.IntSqrt where

import Data.SBV
import Data.SBV.Control

import Data.SBV.Tools.WeakestPreconditions

import GHC.Generics (Generic)

import Prelude hiding (sqrt)

-- * Program state

-- | The state for the division program, parameterized over a base type @a@.
data SqrtS a = SqrtS { x    :: a   -- ^ The input
                     , sqrt :: a   -- ^ The floor of the square root
                     , i    :: a   -- ^ Successive squares, as the sum of j's
                     , j    :: a   -- ^ Successive odds
                     }
                     deriving (Show, Generic, Mergeable, Functor, Foldable, Traversable)

-- | Show instance for 'SqrtS'. The above deriving clause would work just as well,
-- but we want it to be a little prettier here, and hence the @OVERLAPS@ directive.
instance {-# OVERLAPS #-} (SymVal a, Show a) => Show (SqrtS (SBV a)) where
   show (SqrtS x sqrt i j) = "{x = " ++ sh x ++ ", sqrt = " ++ sh sqrt ++ ", i = " ++ sh i ++ ", j = " ++ sh j ++ "}"
     where sh v = maybe "<symbolic>" show (unliteral v)

-- | 'Fresh' instance for the program state
instance SymVal a => Fresh IO (SqrtS (SBV a)) where
  fresh = SqrtS <$> freshVar_  <*> freshVar_ <*> freshVar_ <*> freshVar_

-- | Helper type synonym
type S = SqrtS SInteger

-- * The algorithm

-- | The imperative square-root algorithm, assuming non-negative @x@
--
-- @
--    sqrt = 0                  -- set sqrt to 0
--    i    = 1                  -- set i to 1, sum of j's so far
--    j    = 1                  -- set j to be the first odd number i
--    while i <= x              -- while the sum hasn't exceeded x yet
--      sqrt = sqrt + 1              -- increase the sqrt
--      j    = j + 2                 -- next odd number
--      i    = i + j                 -- running sum of j's
-- @
--
-- Note that we need to explicitly annotate each loop with its invariant and the termination
-- measure. For convenience, we take those two as parameters for simplicity.
algorithm :: Invariant S -> Maybe (Measure S) -> Stmt S
algorithm inv msr = Seq [ assert "x >= 0" $ \SqrtS{x} -> x .>= 0
                        , Assign $ \st -> st{sqrt = 0, i = 1, j = 1}
                        , While "i <= x"
                                inv
                                msr
                                (\SqrtS{x, i} -> i .<= x)
                                $ Seq [ Assign $ \st@SqrtS{sqrt} -> st{sqrt = sqrt + 1}
                                      , Assign $ \st@SqrtS{j}    -> st{j    = j + 2}
                                      , Assign $ \st@SqrtS{i, j} -> st{i    = i + j}
                                      ]
                        ]

-- | Precondition for our program: @x@ must be non-negative. Note that there is an explicit
-- call to 'Data.SBV.Tools.WeakestPreconditions.abort' in our program to protect against this case, so if we do not have this
-- precondition, all programs will fail.
pre :: S -> SBool
pre SqrtS{x} = x .>= 0

-- | Postcondition for our program: The @sqrt@ squared must be less than or equal to @x@, and
-- @sqrt+1@ squared must strictly exceed @x@.
post :: S -> SBool
post SqrtS{x, sqrt} = sq sqrt .<= x .&& sq (sqrt+1) .> x
  where sq n = n * n

-- | Stability condition: Program must leave @x@ unchanged.
noChange :: Stable S
noChange = [stable "x" x]

-- | A program is the algorithm, together with its pre- and post-conditions.
imperativeSqrt :: Invariant S -> Maybe (Measure S) -> Program S
imperativeSqrt inv msr = Program { setup         = return ()
                                 , precondition  = pre
                                 , program       = algorithm inv msr
                                 , postcondition = post
                                 , stability     = noChange
                                 }

-- * Correctness

-- | The invariant is that at each iteration of the loop @sqrt@ remains below or equal
-- to the actual square-root, and @i@ tracks the square of the next value. We also
-- have that @j@ is the @sqrt@'th odd value. Coming up with this invariant is not for
-- the faint of heart, for details I would strongly recommend looking at Manna's seminal
-- /Mathematical Theory of Computation/ book (chapter 3). The @j .> 0@ part is needed
-- to establish the termination.
invariant :: Invariant S
invariant SqrtS{x, sqrt, i, j} = j .> 0 .&& sq sqrt .<= x .&& i .== sq (sqrt + 1) .&& j .== 2*sqrt + 1
  where sq n = n * n

-- | The measure. In each iteration @i@ strictly increases, thus reducing the differential @x - i@
measure :: Measure S
measure SqrtS{x, i} = [x - i]

-- | Check that the program terminates and the post condition holds. We have:
--
-- >>> correctness
-- Total correctness is established.
-- Q.E.D.
correctness :: IO ()
correctness = print =<< wpProveWith defaultWPCfg{wpVerbose=True} (imperativeSqrt invariant (Just measure))
