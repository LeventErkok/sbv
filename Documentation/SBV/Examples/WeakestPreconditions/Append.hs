-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.WeakestPreconditions.Append
-- Copyright : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proof of correctness of an imperative list-append algorithm, using weakest
-- preconditions. Illustrates the use of SBV's symbolic lists together with
-- the WP algorithm.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedLists       #-}
{-# LANGUAGE TypeFamilies          #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.WeakestPreconditions.Append where

import Data.SBV
import Data.SBV.Tools.WeakestPreconditions

import Prelude hiding ((++))
import qualified Prelude as P

import           Data.SBV.List ((++))
import qualified Data.SBV.List as L

import GHC.Generics (Generic)

-- * Program state

-- | The state of the length program, paramaterized over the element type @a@
data AppS a = AppS { xs :: a  -- ^ The first input list
                   , ys :: a  -- ^ The second input list
                   , ts :: a  -- ^ Temporary variable
                   , zs :: a  -- ^ Output
                   }
                   deriving (Generic, Mergeable, Traversable, Functor, Foldable)

-- | Show instance, a bit more prettier than what would be derived:
instance Show (f a) => Show (AppS (f a)) where
  show AppS{xs, ys, ts, zs} = "{xs = " P.++ show xs P.++ ", ys = " P.++ show ys P.++ ", ts = " P.++ show ts P.++ ", zs = " P.++ show zs P.++ "}"

-- | 'Queriable' instance for the program state
instance Queriable IO (AppS (SList Integer)) where
  type QueryResult (AppS (SList Integer)) = AppS [Integer]
  create = AppS <$> freshVar_  <*> freshVar_  <*> freshVar_  <*> freshVar_

-- | Helper type synonym
type A = AppS (SList Integer)

-- * The algorithm

-- | The imperative append algorithm:
--
-- @
--    zs = []
--    ts = xs
--    while not (null ts)
--      zs = zs ++ [head ts]
--      ts = tail ts
--    ts = ys
--    while not (null ts)
--      zs = zs ++ [head ts]
--      ts = tail ts
-- @
algorithm :: Stmt A
algorithm = Seq [ Assign $ \st          -> st{zs = []}
                , Assign $ \st@AppS{xs} -> st{ts = xs}
                , loop "xs" (\AppS{xs, zs, ts} -> xs .== zs ++ ts)
                , Assign $ \st@AppS{ys} -> st{ts = ys}
                , loop "ys" (\AppS{xs, ys, zs, ts} -> xs ++ ys .== zs ++ ts)
                ]
  where loop w inv = While ("walk over " P.++ w)
                           inv
                           (Just (\AppS{ts} -> [L.length ts]))
                           (\AppS{ts} -> sNot (L.null ts))
                           $ Seq [ Assign $ \st@AppS{ts, zs} -> st{zs = zs `L.snoc` L.head ts}
                                 , Assign $ \st@AppS{ts}     -> st{ts = L.tail ts            }
                                 ]

-- | A program is the algorithm, together with its pre- and post-conditions.
imperativeAppend :: Program A
imperativeAppend = Program { setup         = return ()
                           , precondition  = const sTrue  -- no precondition
                           , program       = algorithm
                           , postcondition = postcondition
                           , stability     = noChange
                           }
  where -- We must append properly!
        postcondition :: A -> SBool
        postcondition AppS{xs, ys, zs} = zs .== xs ++ ys

        -- Program should never change values of @xs@ and @ys@
        noChange = [stable "xs" xs, stable "ys" ys]

-- * Correctness

-- | We check that @zs@ is @xs ++ ys@ upon termination.
--
-- >>> correctness
-- Total correctness is established.
-- Q.E.D.
correctness :: IO (ProofResult (AppS [Integer]))
correctness = wpProveWith defaultWPCfg{wpVerbose=True} imperativeAppend
