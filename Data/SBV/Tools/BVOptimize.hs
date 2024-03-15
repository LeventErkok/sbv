-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.BVOptimize
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bit-vector optimization based on linear scan of the bits. The optimization
-- engines are usually not incremental, and they perform poorly for optimizing
-- bit-vector values in the presence of complicated constraints. We implement
-- a simple optimizer by scanning the bits from top-to-bottom to minimize/maximize
-- unsigned bit vector quantities, using the regular (i.e., incremental) solver.
-- This can lead to better performance for this class of problems.
--
-- This implementation is based on an idea by Nikolaj Bjorner, see <https://github.com/Z3Prover/z3/issues/7156>.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.BVOptimize (
            -- ** Maximizing bit-vectors
            -- $maxBVEx
              maxBV, maxBVWith
            -- ** Minimizing bit-vectors
            -- $minBVEx
            , minBV, minBVWith
          ) where

import Control.Monad

import Data.SBV
import Data.SBV.Control

-- $setup
-- >>> -- For doctest purposes only:
-- >>> :set -XDataKinds
-- >>> import Data.SBV

{- $maxBVEx

Here is a simple example of maximizing a bit-vector value:

>>> :{
runSMT $ do x :: SWord 32 <- free "x"
            constrain $ x .> 5
            constrain $ x .< 27
            maxBV False x
:}
Satisfiable. Model:
  x = 26 :: Word32
-}

-- | Maximize the value of an unsigned bit-vector value, using the default solver.
maxBV :: SFiniteBits a
      => Bool                -- ^ Do we want unsat-cores if unsatisfiable?
      -> SBV a               -- ^ Value to maximize
      -> Symbolic SatResult
maxBV = maxBVWith defaultSMTCfg

-- | Maximize the value of an unsigned bit-vector value, using the given solver.
maxBVWith :: SFiniteBits a => SMTConfig -> Bool-> SBV a -> Symbolic SatResult
maxBVWith = minMaxBV True

{- $minBVEx

Here is a simple example of minimizing a bit-vector value:

>>> :{
runSMT $ do x :: SWord 32 <- free "x"
            constrain $ x .> 5
            constrain $ x .< 27
            minBV False x
:}
Satisfiable. Model:
  x = 6 :: Word32
-}

-- | Minimize the value of an unsigned bit-vector value, using the default solver.
minBV :: SFiniteBits a
      => Bool                -- ^ Do we want unsat-cores if unsatisfiable?
      -> SBV a               -- ^ Value to minimize
      -> Symbolic SatResult
minBV = minBVWith defaultSMTCfg

-- | Minimize the value of an unsigned bit-vector value, using the given solver.
minBVWith :: SFiniteBits a => SMTConfig -> Bool-> SBV a -> Symbolic SatResult
minBVWith = minMaxBV False

-- | min/max a given unsigned bit-vector. We walk down the bits in an incremental
-- fashion. If we are maximizing, we try to make the bits set as we go down, otherwise
-- we try to unset them. We keep adding the constraints so long as they are satisfiable,
-- and at the end, get the optimal value produced.
minMaxBV :: SFiniteBits a => Bool -> SMTConfig -> Bool -> SBV a -> Symbolic SatResult
minMaxBV isMax cfg getUC v
 | hasSign v
 = error $ "minMaxBV works on unsigned bitvectors, received: " ++ show (kindOf v)
 | True
 = do when getUC $ setOption $ ProduceUnsatCores True 
      query $ go (blastBE v)
 where uc | getUC = Just <$> getUnsatCore
          | True  = pure Nothing

       rSat   = SatResult . Satisfiable   cfg <$> getModel
       rUnk   = SatResult . Unknown       cfg <$> getUnknownReason
       rUnsat = SatResult . Unsatisfiable cfg <$> uc

       go :: [SBool] -> Query SatResult
       go []     = do r <- checkSat
                      case r of
                        Sat     -> rSat
                        Unsat   -> rUnsat
                        Unk     -> rUnk
                        DSat {} -> error "minMaxBV: Unexpected DSat result"
       go (b:bs) = do push 1
                      if isMax then constrain b
                               else constrain $ sNot b
                      r <- checkSat
                      case r of
                        Sat    -> go bs >>= \res -> pop 1 >> return res
                        Unsat  ->                   pop 1 >> go bs
                        Unk    ->                   pop 1 >> rUnk
                        DSat{} -> error "minMaxBV: Unexpected DSat result"
