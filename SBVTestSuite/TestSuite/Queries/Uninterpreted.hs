-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Queries.Uninterpreted
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing uninterpreted value extraction
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Queries.Uninterpreted where

import Data.SBV.Control
import Utils.SBVTestFramework

data L = A | B
mkSymbolicEnumeration ''L

-- Test suite
tests :: TestTree
tests =
  testGroup "Queries.Uninterpreted"
    [ goldenCapturedIO "qUninterp1" testQuery
    ]

testQuery :: FilePath -> IO ()
testQuery rf = do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} unint1
                  appendFile rf ("\n FINAL:" ++ r ++ "\nDONE!\n")


unint1 :: Symbolic String
unint1 = do (x :: SBV L) <- free_

            query $ do _ <- checkSat
                       show <$> getValue x
