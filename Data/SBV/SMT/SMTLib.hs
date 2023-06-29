-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.SMT.SMTLib
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Conversion of symbolic programs to SMTLib format
-----------------------------------------------------------------------------

{-# LANGUAGE NamedFieldPuns #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.SMT.SMTLib (
          SMTLibPgm
        , toSMTLib
        , toIncSMTLib
        ) where

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
  where cvt v ctx progInfo kindInfo isSat comments qinps consts tbls arrs uis axs asgnsSeq cstrs out config = SMTLibPgm v pgm defs
         where converter   = case v of
                               SMTLib2 -> SMT2.cvt
               (pgm, defs) = converter ctx progInfo kindInfo isSat comments qinps consts tbls arrs uis axs asgnsSeq cstrs out config

-- | Convert to SMTLib-2 format
toIncSMTLib2 :: SMTLibIncConverter [String]
toIncSMTLib2 = cvt SMTLib2
  where cvt SMTLib2 = SMT2.cvtInc
