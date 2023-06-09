-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.NaturalInduction
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proof by induction over naturals.
-----------------------------------------------------------------------------

module Data.SBV.Tools.NaturalInduction (
           inductNat
         , inductNatWith
       ) where

import Data.SBV
import Data.SBV.Tuple

---------------------------------------------------------------------
-- * Induction over natural numbers
---------------------------------------------------------------------

-- | Perform natural induction over the given function, which returns left and
-- right hand-sides to be proven equal. Uses 'defaultSMTCfg'. That is,
-- given @f x = (lhs x, rhs x)@, we inductively establish that @lhs@ and
-- @rhs@ agree on @0@, @1@, ... @n@, i.e., for all non-negative integers.
--
-- >>> import Data.SBV
-- >>> import Data.SBV.Tools.NaturalInduction
-- >>> let sumToN        :: SInteger -> SInteger = smtFunction "sumToN"        $ \x -> ite (x .<= 0) 0 (x   + sumToN        (x-1))
-- >>> let sumSquaresToN :: SInteger -> SInteger = smtFunction "sumSquaresToN" $ \x -> ite (x .<= 0) 0 (x*x + sumSquaresToN (x-1))
-- >>> inductNat $ \n -> (sumToN n, (n*(n+1)) `sEDiv` 2)
-- Q.E.D.
-- >>> inductNat $ \n -> (sumSquaresToN n, (n*(n+1)*(2*n+1)) `sEDiv` 6)
-- Q.E.D.
-- >>> inductNat $ \n -> (sumSquaresToN n, ite (n .== 12) 0 ((n*(n+1)*(2*n+1)) `sEDiv` 6))
-- Falsifiable. Counter-example:
--   P(0)   =     (0,0) :: (Integer, Integer)
--   P(k)   = (506,506) :: (Integer, Integer)
--   P(k+1) =   (650,0) :: (Integer, Integer)
--   k      =        11 :: Integer
inductNat :: SymVal a => (SInteger -> (SBV a, SBV a)) -> IO ThmResult
inductNat = inductNatWith defaultSMTCfg

-- | Perform natural induction over, using the given solver.
inductNatWith :: SymVal a => SMTConfig -> (SInteger -> (SBV a, SBV a)) -> IO ThmResult
inductNatWith cfg p = proveWith cfg $ do
                        k <- free "k"
                        let at0  = observe "P(0)"   (tuple (p 0))
                            atk  = observe "P(k)"   (tuple (p k))
                            atk1 = observe "P(k+1)" (tuple (p (k+1)))
                            p0   = at0^._1  .== at0^._2
                            pk   = atk^._1  .== atk^._2
                            pk1  = atk1^._1 .== atk1^._2
                        constrain $ k .>= 0
                        constrain pk
                        pure $ p0 .&& pk1

{- HLint ignore module "Redundant ^." -}
