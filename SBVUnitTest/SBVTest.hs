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
module SBVTest(generateGoldCheck, showsAs, ioShowsAs, mkTestSuite, SBVTestSuite(..), module Test.HUnit, isThm, isSat, numberOfModels) where

import Data.SBV        (Provable(..), isTheorem, isSatisfiable, AllSatResult(..), allSat)
import Data.Maybe      (fromJust)
import System.FilePath ((</>))
import Test.HUnit      (Test(..), Assertion, assert, (~:), test)

-- | A Test-suite, parameterized by the gold-check generator/checker
data SBVTestSuite = SBVTestSuite ((forall a. Show a => (IO a -> FilePath -> IO ())) -> Test)

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

-- | Check if a property is a theorem, no timeout
isThm :: Provable a => a -> IO Bool
isThm p = fromJust `fmap` isTheorem Nothing p

-- | Check if a property is satisfiable, no timeout
isSat :: Provable a => a -> IO Bool
isSat p = fromJust `fmap` isSatisfiable Nothing p

-- | Count the number of models
numberOfModels :: Provable a => a -> IO Int
numberOfModels p = do AllSatResult (_, rs) <- allSat p
                      return $ length rs
