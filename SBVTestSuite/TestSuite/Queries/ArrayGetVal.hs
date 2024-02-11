-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Queries.ArrayGetVal
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Making sure array get-value works, since we might send extra asserts after
-- check-sat.
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Queries.ArrayGetVal (tests)  where

import Data.SBV.Control

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.ArrayGetVal"
    [ goldenCapturedIO "arrayGetValTest1" testQuery
    ]

testQuery :: FilePath -> IO ()
testQuery rf = do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} t1
                  appendFile rf ("\n FINAL:" ++ show r ++ "\nDONE!\n")

t1 :: Symbolic Integer
t1 = do a :: SArray Integer Integer <- newArray "a" Nothing
        query $ do ensureSat
                   getValue (readArray (writeArray a 1 2) 1)
