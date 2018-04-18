-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Queries.Strings
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Testing a few strings
-----------------------------------------------------------------------------

module TestSuite.Queries.Strings (tests)  where

import Data.SBV
import Data.SBV.Control

import qualified Data.SBV.Char   as C
import qualified Data.SBV.RegExp as R

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.QueryStrings"
    [ goldenCapturedIO "query_Strings1" $ testQuery qs1
    , goldenCapturedIO "query_Chars1"   $ testQuery qc1
    ]

testQuery :: Show a => Symbolic a -> FilePath -> IO ()
testQuery t rf = do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} t
                    appendFile rf ("\nFINAL OUTPUT:\n" ++ show r ++ "\n")

qs1 :: Symbolic [String]
qs1 = do a <- sString "a"

         constrain $ a `R.match` RE_Loop 5 5 (RE_Literal "xyz")

         query $ do _ <- checkSat
                    s <- getValue a
                    if s == concat (replicate 5 "xyz")
                       then return [s]
                       else error $ "Didn't expect this: " ++ show s

qc1 :: Symbolic Char
qc1 = do a <- sChar "a"

         constrain $ C.ord a .>= 65
         constrain $ C.ord a .<  66

         query $ do _ <- checkSat
                    s <- getValue a
                    if s == 'A'
                       then return s
                       else error $ "Didn't expect this: " ++ show s
