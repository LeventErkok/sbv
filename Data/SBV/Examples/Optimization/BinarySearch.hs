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


data BSOpts a =
  BSOpts
  { getBounds :: IO (a,a)
  , getNext :: a -> a -> IO (Maybe a)
  }

class DefaultBSOpts a where
  defaultBSOpts :: BSOpts a


instance (Bounded a, Integral a) => DefaultBSOpts a where
  defaultBSOpts = BSOpts
    { getBounds = return (minBound, maxBound)
    , getNext = (\lower upper ->
       if | upper <= lower+1 -> return Nothing
          | otherwise        -> return $ Just $ (lower `div` 2) + (upper `div` 2)
         )
    }

instance DefaultBSOpts Integer where
  defaultBSOpts = BSOpts
    { getBounds = return (-1,1)
    , getNext = (\_ _ -> return Nothing) }

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

puzzle :: IO Int32
puzzle = binarySearchWith z3 defaultBSOpts p
  where
    p :: Int32 -> Predicate
    p x =
      let
        sx :: SInt32
        sx = fromIntegral x
      in return $ sx .>= 20000

binarySearchWith ::
     SMTConfig
  -> BSOpts a
  -> (a -> Predicate)
  -> IO a
binarySearchWith cfg opts pred0 = do
  (lower, upper) <- getBounds opts
  go lower upper

  where
    go lower upper = do
      let quit = return upper
      mm <- getNext opts lower upper
      case mm of
        Nothing           -> quit
        (Just middle) -> do
          (SatResult ans) <- satWith cfg $ pred0 middle
          case ans of
            Satisfiable _ _ -> go lower middle
            Unsatisfiable _ -> go middle upper
            _               -> quit
