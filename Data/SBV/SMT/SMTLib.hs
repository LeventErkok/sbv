-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.SMT.SMTLib
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Conversion of symbolic programs to SMTLib format
-----------------------------------------------------------------------------

{-# LANGUAGE NamedFieldPuns #-}

module Data.SBV.SMT.SMTLib (
          SMTLibPgm
        , toSMTLib
        , toIncSMTLib
        ) where

import qualified Data.Set as Set (member, toList)

import Data.SBV.Core.Data

import Data.SBV.SMT.Utils
import qualified Data.SBV.SMT.SMTLib2 as SMT2

-- | Convert to SMT-Lib, in a full program context.
toSMTLib :: SMTConfig -> SMTLibConverter SMTLibPgm
toSMTLib SMTConfig{smtLibVersion} = case smtLibVersion of
                                      SMTLib2 -> toSMTLib2

-- | Convert to SMT-Lib, in an incremental query context.
toIncSMTLib :: SMTConfig -> SMTLibIncConverter [String]
toIncSMTLib SMTConfig{smtLibVersion} = case smtLibVersion of
                                         SMTLib2 -> toIncSMTLib2

-- | Convert to SMTLib-2 format
toSMTLib2 :: SMTLibConverter SMTLibPgm
toSMTLib2 = cvt SMTLib2
  where cvt v kindInfo isSat comments qinps skolemMap consts tbls arrs uis axs asgnsSeq cstrs out config
         | KUnbounded `Set.member` kindInfo && not (supportsUnboundedInts solverCaps)
         = unsupported "unbounded integers"
         | KReal `Set.member` kindInfo  && not (supportsReals solverCaps)
         = unsupported "algebraic reals"
         | (needsFloats || needsDoubles) && not (supportsIEEE754 solverCaps)
         = unsupported "floating-point numbers"
         | needsQuantifiers && not (supportsQuantifiers solverCaps)
         = unsupported "quantifiers"
         | not (null sorts) && not (supportsUninterpretedSorts solverCaps)
         = unsupported "uninterpreted sorts"
         | True
         = SMTLibPgm v pgm
         where sorts = [s | KUserSort s _ <- Set.toList kindInfo]
               solverCaps = capabilities (solver config)
               unsupported w = error $ unlines [ "SBV: Given problem needs " ++ w
                                               , "*** Which is not supported by SBV for the chosen solver: " ++ show (name (solver config))
                                               ]
               converter = case v of
                             SMTLib2 -> SMT2.cvt
               pgm = converter kindInfo isSat comments qinps skolemMap consts tbls arrs uis axs asgnsSeq cstrs out config

               needsFloats  = KFloat  `Set.member` kindInfo
               needsDoubles = KDouble `Set.member` kindInfo
               needsQuantifiers
                 | isSat = ALL `elem` quantifiers
                 | True  = EX  `elem` quantifiers
                 where quantifiers = map fst qinps

-- | Convert to SMTLib-2 format
toIncSMTLib2 :: SMTLibIncConverter [String]
toIncSMTLib2 = cvt SMTLib2
  where cvt SMTLib2 = SMT2.cvtInc
