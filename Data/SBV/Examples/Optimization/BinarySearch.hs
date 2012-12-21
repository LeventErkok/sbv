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

instance (Bounded a, Integral a) => DefaultBSOpts a where
  defaultBSOpts = BSOpts
    { bsBounds = (\_ _ -> return (minBound, maxBound))
    , bsNext = (\lower upper ->
       if | upper <= lower+1 -> Nothing
          | otherwise        -> Just $
              ((lower+1) `div` 2) + (upper `div` 2)
         )
    }

instance DefaultBSOpts Integer where
  defaultBSOpts = BSOpts
    { bsBounds = \_ _ -> return (-1,1)
    , bsNext = (\_ _ -> Nothing) }

puzzle :: IO Int32
puzzle = binarySearchWith z3 defaultBSOpts p
  where
    p :: Int32 -> Predicate
    p x =
      let
        sx :: SInt32
        sx = fromIntegral x
      in return $ sx .>= 20000

-- | Given an @a -> Predicate@ that satisfies
-- @x < y &&&  pred0 x ==> pred0 y@,
-- finds a value @x@ of type @a@ such that
-- @
--   forall x' <= x - torelance . pred0 x' is unsatisfiable.
--   forall x' >= x             . pred0 x' is satisfiable.
-- @
--
-- >>> puzzle
-- 20000

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
