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

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}

module Documentation.SBV.Examples.ProofTools.WPSum where

import Data.SBV
import Data.SBV.Control

import Data.SBV.Tools.WeakestPreconditions

data SumS a = SumS { i, s, n :: a }

instance Show (SumS SInteger) where
   show (SumS i s n) = "{n = " ++ sh n ++ ", i = " ++ sh i ++ ", s = " ++ sh s ++ "}"
     where sh v = case unliteral v of
                    Nothing -> "<symbolic>"
                    Just l  -> show l

instance Show (SumS Integer) where
   show (SumS i s n) = show (SumS (literal i) (literal s) (literal n))

instance Queriable IO (SumS SInteger) (SumS Integer) where
 create                = SumS <$> freshVar_  <*> freshVar_  <*> freshVar_
 project SumS{i, s, n} = SumS <$> getValue i <*> getValue s <*> getValue n
 embed   SumS{i, s, n} = return $ SumS (literal i) (literal s) (literal n)

type I  = Integer
type SI = SBV I

iSum :: (SumS SI -> SBool) -> Prog (SumS SI)
iSum inv = Seq [ Assign $ \st -> st{i = 0, s = 0}
               , While "i <= n"
                       inv
                       (\SumS{n, i} -> n - i + 1)
                       (\SumS{n, i} -> i .<= n)
                       $ Seq [ Assign $ \st@SumS{s, i} -> st{s = s+i}
                             , Assign $ \st@SumS{i}    -> st{i = i+1}
                             ]
               ]

inv1, inv2, inv3, inv4, inv5, inv6, inv7, inv8 :: SumS SI -> SBool
inv1 _          = sFalse
inv2 _          = sTrue
inv3 SumS{n}    = n .>= 0
inv4 SumS{i, n} = i .<= n+1
inv5 SumS{s, i} = s .== (i * (i-1)) `sDiv` 2
inv6 s          = inv3 s .=> inv4 s
inv7 s          = inv3 s .=> inv5 s
inv8 s          = inv3 s .=> inv4 s .&& inv5 s

-- | Correctness proof
--
-- >>> correctness inv1
-- >>> correctness inv2
-- >>> correctness inv3
-- >>> correctness inv4
-- >>> correctness inv5
-- >>> correctness inv6
-- >>> correctness inv7
-- >>> correctness inv8
correctness :: (SumS SI -> SBool) -> IO (ProofResult (SumS I))
correctness inv = checkWith z3{verbose=False} True (iSum inv) prop
  where prop SumS{s, n} = n .>= 0 .=> s .== (n * (n+1)) `sDiv` 2
