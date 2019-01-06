-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Misc.Tuple
-- Author    : Joel Burget, Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Some tuple examples.
-----------------------------------------------------------------------------

{-# LANGUAGE TypeApplications #-}

module Documentation.SBV.Examples.Misc.Tuple where

import Data.SBV
import Data.SBV.Tuple

example :: IO SatResult
example = sat $ do
  [ab, cd] <- sTuples @(Integer, Integer, Integer) ["ab", "cd"]
  constrain $ ab^._1 .== cd^._2
  constrain $ ab^._2 .== cd^._1
