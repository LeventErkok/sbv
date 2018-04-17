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

import Data.SBV.Control
import qualified Data.SBV.Tools.SString as S

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.QueryStrings"
    [ goldenCapturedIO "query_Strings1" $ testQuery q1
    ]

testQuery :: Show a => Symbolic a -> FilePath -> IO ()
testQuery t rf = do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} t
                    appendFile rf ("\nFINAL OUTPUT:\n" ++ show r ++ "\n")

q1 :: Symbolic [String]
q1 = do a <- sString "a"

        constrain $ a `S.match` RE_Loop 5 5 (RE_Literal "xyz")

        query $ do _ <- checkSat
                   s <- getValue a
                   if s == concat (replicate 5 "xyz")
                      then return [s]
                      else error $ "Didn't expect this: " ++ show s
