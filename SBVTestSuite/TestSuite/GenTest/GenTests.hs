-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.GenTest.GenTests
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test-suite for generating tests
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.GenTest.GenTests(tests) where

import Data.SBV.Tools.GenTest

import System.Random

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "GenTest.GenTests"
   [ goldenCapturedIO "tgen_haskell" $ render (Haskell "haskTest")
   , goldenCapturedIO "tgen_c"       $ render (C       "CTest")
   , goldenCapturedIO "tgen_forte"   $ render (Forte   "ForteTest" True ([32,32], [32,32,32]))
   ]
 where simple = genTest 10 $ do x <- sWord32 "x"
                                y <- sWord32 "y"
                                return (x+y, x-y, x*y)
       render s f = do setStdGen (mkStdGen 0)  -- make sure we always get the same results!
                       r <- renderTest s <$> simple
                       writeFile f r
