-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Optimization.Binary
-- Copyright   :  (c) Levent Erkok, Takayuki Muranushi
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com, muranushi@gmail.com
-- Stability   :  experimental
--
--

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.SBV.Examples.Optimization.BinarySearch where

import Data.SBV

type BSPred a = a -> Predicate
type BSBounds a = SMTConfig -> BSPred a -> IO (a,a)
type BSNext a = a -> a -> Maybe a

data BSOpts a =
  BSOpts
  { bsBounds :: BSBounds a
  , bsNext :: BSNext a
  }

class DefaultBSOpts a where
  defaultBSOpts :: BSOpts a

bsBoundsBounded :: (Bounded a) => BSBounds a
bsBoundsBounded _cfg _pred0 = return (minBound, maxBound)

bsBoundsSearch :: (Num a) => BSBounds a
bsBoundsSearch cfg pred0 = do
  lower <- goDown (-1)
  upper <- goUp 1
  return (lower, upper)
    where
      goUp x = do
        (SatResult ans) <- satWith cfg $ pred0 x
        case ans of
          Satisfiable _ _ -> return x
          _               -> goUp $ 2*x
      goDown x = do
        (SatResult ans) <- satWith cfg $ pred0 x
        case ans of
          Unsatisfiable  _ -> return x
          _                -> goDown $ 2*x



bsNextIntegral :: (Integral a) => BSNext a
bsNextIntegral lower upper
  | upper <= lower+1 = Nothing
  | otherwise        =
        Just $ ((lower+1) `div` 2) + (upper `div` 2)

bsNextFractional :: (Ord a, Fractional a) => BSNext a
bsNextFractional lower upper
  | upper <= lower+1e-16 = Nothing
  | otherwise = Just $ (lower+upper)/2


instance DefaultBSOpts Int32 where
  defaultBSOpts = BSOpts
    { bsBounds = bsBoundsBounded
    , bsNext   = bsNextIntegral
    }



instance DefaultBSOpts Integer where
  defaultBSOpts = BSOpts
    { bsBounds = bsBoundsSearch
    , bsNext = bsNextIntegral }

instance DefaultBSOpts Rational where
  defaultBSOpts = BSOpts
    { bsBounds = bsBoundsSearch
    , bsNext = bsNextFractional }


puzzle :: IO Integer
puzzle = binarySearchWith z3 defaultBSOpts p
  where
    p :: Integer -> Predicate
    p x =
      let
        sx :: SInteger
        sx = fromIntegral x
      in return $ sx * sx .>= 30000000000000000

-- | Given an @a -> Predicate@ that satisfies
-- @x < y &&&  pred0 x ==> pred0 y@,
-- finds a value @x@ of type @a@ such that
-- @
--   forall x' <= x - torelance . pred0 x' is unsatisfiable.
--   forall x' >= x             . pred0 x' is satisfiable.
-- @
--
-- >>> puzzle
-- 173205081

binarySearchWith ::
     SMTConfig
  -> BSOpts a
  -> BSPred a
  -> IO a
binarySearchWith cfg opts pred0 = do
  (lower, upper) <- bsBounds opts cfg pred0
  go lower upper

  where
    go lower upper = do
      let quit = return upper
      case bsNext opts lower upper of
        Nothing           -> quit
        (Just middle) -> do
          (SatResult ans) <- satWith cfg $ pred0 middle
          case ans of
            Satisfiable _ _ -> go lower middle
            Unsatisfiable _ -> go middle upper
            _               -> quit
