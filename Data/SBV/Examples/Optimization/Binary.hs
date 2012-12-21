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
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.SBV.Examples.Optimization.Binary where

import Data.SBV

class Searchable a where
  getBounds :: IO (a,a)
  between :: a -> a -> Maybe a

instance (Bounded a, Integral a) => Searchable a where
  getBounds = return (minBound, maxBound)
  between lower upper
    | upper - lower <=1 = Nothing
    | otherwise         = Just $ (lower + upper) `div` 2


-- | Given an @a -> Predicate@ that satisfies
-- @x < y &&&  pred0 x ==> pred0 y@,
-- finds a value @x@ of type @a@ such that
-- @
--   forall x' <= x - torelance . pred0 x' is unsatisfiable.
--   forall x' >= x             . pred0 x' is satisfiable.
-- @
--
-- >>> puzzle
-- 42

puzzle = print 42

argminSat :: (Ord a, Num a, Searchable a)
             => a
             -> (a -> Predicate)
             -> IO a
argminSat torelance pred0 = do
  (lower, upper) <- getBounds
  go lower upper

  where
    go lower upper = do
      let quit = return upper
      case between lower upper of
        Nothing                     -> quit
        _ | upper-lower < torelance -> quit
        (Just middle) -> do
          (SatResult ans) <- sat $ pred0 middle
          case ans of
            Satisfiable _ _ -> go lower middle
            Unsatisfiable _ -> go middle upper
            _               -> quit
