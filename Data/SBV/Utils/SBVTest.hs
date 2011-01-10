-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Utils.SBVTest
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Integration with HUnit-based test suite for SBV
-----------------------------------------------------------------------------

{-# LANGUAGE RankNTypes #-}
module Data.SBV.Utils.SBVTest(generateGoldCheck, showsAs, ioShowsAs, mkTestSuite, SBVTestSuite(..), module Test.HUnit) where

import System.FilePath((</>))
import Test.HUnit hiding(State)

data SBVTestSuite = SBVTestSuite ((forall a. Show a => (IO a -> FilePath -> IO ())) -> Test)

mkTestSuite :: ((forall a. (Show a) => IO a -> FilePath -> IO ()) -> Test) -> SBVTestSuite
mkTestSuite = SBVTestSuite

showsAs :: Show a => a -> String -> Assertion
showsAs r s = assert $ show r == s

ioShowsAs :: Show a => IO a -> String -> Assertion
ioShowsAs r s = do v <- r
                   assert $ show v == s

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
