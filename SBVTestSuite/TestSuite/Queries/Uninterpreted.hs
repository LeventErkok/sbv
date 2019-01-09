-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Queries.Uninterpreted
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing uninterpreted value extraction
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TestSuite.Queries.Uninterpreted where

import Data.Generics
import Data.SBV.Control

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Queries.Uninterpreted"
    [ goldenCapturedIO "qUninterp1" testQuery
    ]

testQuery :: FilePath -> IO ()
testQuery rf = do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} unint1
                  appendFile rf ("\n FINAL:" ++ r ++ "\nDONE!\n")


data L = A | B ()
       deriving (Eq, Ord, Show, Read, Data)

instance SymVal L
instance HasKind L
instance SMTValue L

unint1 :: Symbolic String
unint1 = do (x :: SBV L) <- free_

            query $ do _ <- checkSat
                       getUninterpretedValue x
