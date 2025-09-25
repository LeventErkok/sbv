-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Queries.Enums
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.Uninterpreted.AUF
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Queries.Enums where

import Data.SBV.Control

import Utils.SBVTestFramework

data BinOp  = Plus | Minus | Times deriving (Enum, Bounded, Ord, Eq)
mkSymbolic [''BinOp]

-- Test suite
tests :: TestTree
tests =
  testGroup "Queries.Enums"
    [ goldenCapturedIO "qEnum1" $ \rf -> runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} test
    ]


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
