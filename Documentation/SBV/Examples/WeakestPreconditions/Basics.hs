-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.WeakestPreconditions.Basics
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Some basic aspects of weakest preconditions, demostrating programs
-- that do not use while loops. We use a simple increment program as
-- an example.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}

module Documentation.SBV.Examples.WeakestPreconditions.Basics where

import Data.SBV
import Data.SBV.Control

import Data.SBV.Tools.WeakestPreconditions

import GHC.Generics (Generic)

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
     where sh v = case unliteral v of
                    Nothing -> "<symbolic>"
                    Just l  -> show l

-- | 'Fresh' instance for the program state
instance (SymVal a, SMTValue a) => Fresh IO (IncS (SBV a)) where
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

-- | Precondition for our program. Nothing.
pre :: I -> SBool
pre _ = sTrue

-- | Postcondition for our program: @y@ must @x+1@.
post :: I -> SBool
post IncS{x, y} = y .== x+1

-- | A program is the algorithm, together with its pre- and post-conditions.
imperativeInc :: Stmt I -> Stmt I -> Program I
imperativeInc before after = Program { precondition  = pre
                                     , program       = algorithm before after
                                     , postcondition = post
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
