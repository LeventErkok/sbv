-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Queries.Tuples
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Testing tuple queries
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Queries.Tuples (tests)  where

import Data.SBV
import Data.SBV.Control
import Data.SBV.Tuple

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.QueryTuples"
    [ goldenCapturedIO "query_Tuples1" $ testQuery queryTuples1
    , goldenCapturedIO "query_Tuples2" $ testQuery queryTuples2
    ]

testQuery :: Show a => Symbolic a -> FilePath -> IO ()
testQuery t rf = do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} t
                    appendFile rf ("\nFINAL OUTPUT:\n" ++ show r ++ "\n")

queryTuples1 :: Symbolic (Integer, Char)
queryTuples1 = do
  a <- sTuple @(Integer, Char) "a"

  constrain $ a^._1 .== 1

  query $ do
    _ <- checkSat

    av <- getValue a

    if fst av == 1
       then return av
       else error $ "Didn't expect this: " ++ show av

queryTuples2 :: Symbolic (Integer, (Char, ()))
queryTuples2 = do
  a <- sTuple @(Integer, (Char, ())) "a"

  constrain $ a^._2^._1 .== literal 'c'

  query $ do
    _ <- checkSat

    av@(_, (c, _)) <- getValue a

    if c == 'c'
       then return av
       else error $ "Didn't expect this: " ++ show av

{- HLint ignore module "Use ."        -}
{- HLint ignore module "Redundant ^." -}
