-----------------------------------------------------------------------------
-- |
-- Module      :  SBVTest
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Integration with HUnit-based test suite for SBV
-----------------------------------------------------------------------------

{-# LANGUAGE RankNTypes #-}
module SBVTest(
          generateGoldCheck, showsAs, ioShowsAs, mkTestSuite, SBVTestSuite(..)
        , runSAT, numberOfModels
        , assertIsThm, assertIsntThm, assertIsSat, assertIsntSat
        , module Test.Tasty
        , module Test.Tasty.HUnit
        , goldenVsStringShow
        , goldenCapturedIO
        , module Test.HUnit
        , module Data.SBV
        ) where

import Data.SBV                (SMTConfig(..), Provable(..), isTheorem, isTheoremWith, isSatisfiable, AllSatResult(..), allSat, SymWord(free), SymArray(newArray), defaultSMTCfg)
import Data.SBV.Internals      (runSymbolic, Symbolic, Result)

import qualified Data.ByteString.Lazy.Char8 as LBC

import System.FilePath         ((</>))
import Test.Tasty              (testGroup, TestTree, TestName)
import Test.Tasty.Golden       (goldenVsString)
import Test.Tasty.HUnit        (assert, Assertion, testCase)
import Test.HUnit              (Test(..), (~:), test)

import System.IO.Silently      (capture_)

-- | A Test-suite, parameterized by the gold-check generator/checker
newtype SBVTestSuite = SBVTestSuite ((forall a. Show a => (IO a -> FilePath -> IO ())) -> Test)

-- | Wrap over 'SBVTestSuite', avoids exporting the constructor
mkTestSuite :: ((forall a. (Show a) => IO a -> FilePath -> IO ()) -> Test) -> SBVTestSuite
mkTestSuite = SBVTestSuite

-- | Checks that a particular result shows as @s@
showsAs :: Show a => a -> String -> Assertion
showsAs r s = assert $ show r == s

-- | Run an IO computation and check that it's result shows as @s@
ioShowsAs :: Show a => IO a -> String -> Assertion
ioShowsAs r s = do v <- r
                   assert $ show v == s

-- TODO: Need to use tasty.golden's fascility for generating golden file instead

goldDir2 :: FilePath
goldDir2 = "SBVUnitTest/GoldFiles/"

goldenVsStringShow :: Show a => TestName -> IO a -> TestTree
goldenVsStringShow n res = goldenVsString n (goldDir2 ++ n ++ ".gold") (fmap (LBC.pack . show) res)

-- Run an IO action, capture it's stdout, and make that a test
goldenCapturedIO :: TestName -> IO () -> TestTree
goldenCapturedIO n res = goldenVsString n gf (fmap (LBC.pack) (capture_ res))
  where gf = goldDir2 ++ n ++ ".gold"

-- | Create a gold file for the test case
generateGoldCheck :: FilePath -> Bool -> (forall a. Show a => IO a -> FilePath -> IO ())
generateGoldCheck goldDir shouldCreate action goldFile
  | shouldCreate = do v <- action
                      writeFile gf (show v)
                      putStrLn $ "\nCreated Gold File: " ++ show gf
                      assert True
  | True         = do v <- action
                      g <- readFile gf
                      assert $ show v == g
 where gf = goldDir </> goldFile

-- | Count the number of models
numberOfModels :: Provable a => a -> IO Int
numberOfModels p = do AllSatResult (_, _, rs) <- allSat p
                      return $ length rs

-- | Symbolicly run a SAT instance using the default config
runSAT :: Symbolic a -> IO Result
runSAT = runSymbolic (True, defaultSMTCfg)

-- | Turn provable to an assertion, theorem case
assertIsThm :: Provable a => a -> Assertion
assertIsThm t = assert (isTheorem t)

-- | Turn provable to a negative assertion, theorem case
assertIsntThm :: Provable a => a -> Assertion
assertIsntThm t = assert (fmap not (isTheorem t))

-- | Turn provable to an assertion, satisfiability case
assertIsSat :: Provable a => a -> Assertion
assertIsSat p = assert (isSatisfiable p)

-- | Turn provable to a negative assertion, satisfiability case
assertIsntSat :: Provable a => a -> Assertion
assertIsntSat p = assert (fmap not (isSatisfiable p))
