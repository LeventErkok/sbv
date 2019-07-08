-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Queries.Lists
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing a few lists
-----------------------------------------------------------------------------

{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Queries.Lists (tests)  where

import Data.SBV
import Data.SBV.Control

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.QueryLists"
    [ goldenCapturedIO "query_Lists1" $ testQuery queryLists1
    ]

testQuery :: Show a => Symbolic a -> FilePath -> IO ()
testQuery t rf = do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} t
                    appendFile rf ("\nFINAL OUTPUT:\n" ++ show r ++ "\n")

queryLists1 :: Symbolic [Integer]
queryLists1 = do a :: SList Integer <- sList "a"

                 constrain $ a .== [1..5]

                 query $ do _ <- checkSat

                            av <- getValue a

                            if av == [1..5]
                               then return av
                               else error $ "Didn't expect this: " ++ show av
