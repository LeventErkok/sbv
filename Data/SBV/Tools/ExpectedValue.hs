-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Tools.ExpectedValue
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Computing the expected value of a symbolic variable
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.SBV.Tools.ExpectedValue (expectedValue) where

import Data.Maybe    (fromMaybe, isNothing)
import System.Random (newStdGen, StdGen)

import Data.SBV.BitVectors.Data

-- | Given a symbolic computation that produces a value, compute the
-- expected value that value would take if this computation is run
-- with its free variables drawn from uniform distributions of its
-- respective values, satisfying the given constraints specified by
-- 'constrain' and 'pConstrain' calls.
expectedValue :: forall a. (SymWord a) => Symbolic (SBV a) -> IO Double
expectedValue m
  | isNothing (mbMaxBound :: Maybe a)
  = error "Cannot compute expected-values for unbounded integer results."
  | True
  = warmup warmupCount 0 >>= go warmupCount
  where warmupCount :: Int
        warmupCount = 5000
        epsilon :: Double
        epsilon = 0.001
        warmup :: Int -> Integer -> IO Integer
        warmup 0 v = return v
        warmup n v = do g <- newStdGen
                        t <- runOnce g
                        let v' = v+t
                        v' `seq` warmup (n-1) v'
        runOnce :: StdGen -> IO Integer
        runOnce g = do (_, Result _ _ _ _ cs _ _ _ _ _ cstrs os) <- runSymbolic' (Concrete g) (m >>= output)
                       let cval = fromMaybe (error "Cannot compute expected-values in the presence of uninterpreted constants!") . (`lookup` cs)
                           cond = all (cwToBool . cval) cstrs
                       if cond
                          then case os of
                                [o] -> let cw = cval o
                                       in case (cwSigned cw, cwSize cw) of
                                            (False, Size (Just 1)) -> return $ if cwToBool cw then 1 else 0
                                            _                      -> return $ cwVal cw
                                _    -> error "SBV.expectedValue: Extra calls to output not supported."
                          else runOnce g -- constraint not satisfied try again with the same set of constraints
        go cases curSum = do g <- newStdGen
                             t <- runOnce g
                             let newSum :: Integer
                                 newSum = curSum + t
                                 newCases :: Int
                                 newCases = cases + 1
                                 curEV, newEV :: Double
                                 curEV = fromIntegral curSum / fromIntegral cases
                                 newEV = fromIntegral newSum / fromIntegral newCases
                             if abs (newEV - curEV) < epsilon
                                then return newEV
                                else go newCases newSum
