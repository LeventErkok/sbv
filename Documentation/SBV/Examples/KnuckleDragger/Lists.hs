-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.Lists
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Various KnuckleDragger proofs about lists
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeAbstractions #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.Lists where

import Data.SBV
import qualified Data.SBV.List as L
import Data.SBV.Tools.KnuckleDragger

-- | A list of booleans is not all true, if any of them is false. We have:
--
-- >>> allAny
allAny :: IO Proof
allAny = runKD $ lemma "allAny" (\(Forall @"xs" xs) -> p xs) [induct p]
  where p xs = sNot (L.all id xs) .== L.any sNot xs
