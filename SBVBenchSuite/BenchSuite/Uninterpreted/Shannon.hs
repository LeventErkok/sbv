-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Uninterpreted.Shannon
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Uninterpreted.Shannon
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}
{-# LANGUAGE ScopedTypeVariables #-}

module BenchSuite.Uninterpreted.Shannon(benchmarks) where

import Documentation.SBV.Examples.Uninterpreted.Shannon
import Data.SBV

import BenchSuite.Bench.Bench

benchmarks :: Runner
benchmarks = rGroup
  [ run "shannon"  _shannon  `using` runner proveWith
  , run "shannon2" _shannon2 `using` runner proveWith
  , run "noWiggle" _noWiggle `using` runner proveWith
  , run "univOk"   _univOK   `using` runner proveWith
  , run "existsOk" _existsOK `using` runner proveWith
  ]
  where _shannon  = \x y z -> f x y z .== (x .&& pos f y z .|| sNot x .&& neg f y z)
        _shannon2 = \x y z -> f x y z .== ((x .|| neg f y z) .&& (sNot x .|| pos f y z))
        _noWiggle = \y z -> sNot (f' y z) .<=> pos f y z .== neg f y z
        _univOK   = \y z -> f'' y z .=> pos f y z .&& neg f y z
        _existsOK = \y z -> f''' y z .=> pos f y z .|| neg f y z


f :: Ternary
f    = uninterpret "f"
f', f'', f''' :: Binary
f'   = derivative f
f''  = universal f
f''' = existential f
