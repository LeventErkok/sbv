-----------------------------------------------------------------------------
-- |
-- Module      :  Utils.SBVTestFramework
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Various goodies for testing SBV
-----------------------------------------------------------------------------

{-# LANGUAGE    RankNTypes          #-}
{-# LANGUAGE    ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans   #-}

module Utils.SBVTestFramework (
          showsAs
        , runSAT, numberOfModels
        , assertIsThm, assertIsntThm, assertIsSat, assertIsntSat
        , goldenString
        , goldenVsStringShow
        , goldenCapturedIO
        -- module exports to simplify life
        , module Test.Tasty
        , module Test.Tasty.HUnit
        , module Data.SBV
        ) where

import qualified Control.Exception as C

import qualified Data.ByteString.Lazy.Char8 as LBC

import System.Directory   (removeFile)
import Test.Tasty         (testGroup, TestTree, TestName)
import Test.Tasty.Golden  (goldenVsString, goldenVsFile)
import Test.Tasty.HUnit   (assert, Assertion, testCase)

import Data.SBV

import Data.SBV.Internals (runSymbolic, Symbolic, Result, SBV(..))

-- We don't export this out of anywhere, but is darn useful within tests!
instance Show (SBV a) where
  show (SBV a) = show a

-- | Checks that a particular result shows as @s@
showsAs :: Show a => a -> String -> Assertion
showsAs r s = assert $ show r == s

-- TODO: Need to use tasty.golden's fascility for generating golden file instead

goldDir2 :: FilePath
goldDir2 = "SBVTestSuite/GoldFiles/"

goldenString :: TestName -> IO String -> TestTree
goldenString n res = goldenVsString n (goldDir2 ++ n ++ ".gold") (fmap LBC.pack res)

goldenVsStringShow :: Show a => TestName -> IO a -> TestTree
goldenVsStringShow n res = goldenVsString n (goldDir2 ++ n ++ ".gold") (fmap (LBC.pack . show) res)

goldenCapturedIO :: TestName -> (FilePath -> IO ()) -> TestTree
goldenCapturedIO n res = goldenVsFile n gf gfTmp (rm gfTmp >> res gfTmp)
  where gf    = goldDir2 ++ n ++ ".gold"
        gfTmp = gf ++ "_temp"

        rm f = removeFile f `C.catch` (\(_ :: C.SomeException) -> return ())

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
