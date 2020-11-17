-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Misc.NestedArray
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrates how to model nested-arrays, i.e., arrays of arrays in SBV.
-- Instead of SMTLib's nested model, in SBV we use a tuple as an index,
-- which is isomorphic to nested arrays.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Misc.NestedArray where

import Data.SBV
import Data.SBV.Tuple
import Data.SBV.Control

-- | Model a nested array that is indexed by integers, and we store
-- another integer to integer array in each index. We have:
--
-- >>> nestedArray
-- (0,10)
nestedArray :: IO (Integer, Integer)
nestedArray = runSMT $ do
  idx <- sInteger "idx"
  arr <- newArray_ Nothing :: Symbolic (SArray (Integer, Integer) Integer)

  -- we'll assert that arr[idx][idx] = 10
  let val = readArray arr (tuple (idx, idx))
  constrain $ val .== literal 10

  query $ do
    cs <- checkSat
    case cs of
      Sat -> do idxVal <- getValue idx
                elt    <- getValue (readArray arr (tuple (idx, idx)))
                pure (idxVal, elt)
      _   -> error $ "Solver said: " ++ show cs
