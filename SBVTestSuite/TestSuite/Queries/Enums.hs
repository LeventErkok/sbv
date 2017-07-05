-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Queries.Enums
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for Data.SBV.Examples.Uninterpreted.AUF
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DeriveAnyClass      #-}

module TestSuite.Queries.Enums where

import Data.Generics
import Data.SBV.Control

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Queries.Enums"
    [ goldenCapturedIO "qEnum1" $ \rf -> runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} test
    ]

data BinOp  = Plus | Minus | Times deriving (Eq, Ord, Show, Read, Data, SymWord, HasKind, SMTValue)
type SBinOp = SBV BinOp

test :: Symbolic ()
test = do (p :: SBinOp) <- free "p"
          (m :: SBinOp) <- free "m"
          (t :: SBinOp) <- free "t"

          constrain $ p .<= m
          constrain $ m .<= t
          constrain $ distinct [p, m, t]

          query $ do _ <- checkSat
                     _ <- getValue p
                     _ <- getValue m
                     _ <- getValue t
                     return ()
