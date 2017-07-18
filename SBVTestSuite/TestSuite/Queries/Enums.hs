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

{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TestSuite.Queries.Enums where

import Data.SBV.Control

import Utils.SBVTestFramework

data BinOp  = Plus | Minus | Times
mkSymbolicEnumeration ''BinOp

-- Test suite
tests :: TestTree
tests =
  testGroup "Queries.Enums"
    [ goldenCapturedIO "qEnum1" $ \rf -> runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} test
    ]

type SBinOp = SBV BinOp

test :: Symbolic ()
test = do p :: SBinOp <- free "p"
          m :: SBinOp <- free "m"
          t :: SBinOp <- free "t"

          constrain $ p .<= m
          constrain $ m .<= t
          constrain $ distinct [p, m, t]

          query $ do _ <- checkSat
                     _ <- getValue p
                     _ <- getValue m
                     _ <- getValue t
                     return ()
