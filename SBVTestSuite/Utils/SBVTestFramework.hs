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

{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Utils.SBVTestFramework (
          showsAs
        , runSAT, numberOfModels
        , assertIsThm, assertIsntThm, assertIsSat, assertIsntSat
        , goldenString
        , goldenVsStringShow
        , goldenCapturedIO
        , TravisOS(..), TestEnvironment(..), getTestEnvironment
        , pickTests
        -- module exports to simplify life
        , module Test.Tasty
        , module Test.Tasty.HUnit
        , module Data.SBV
        ) where

import qualified Control.Exception as C

import qualified Data.ByteString.Lazy.Char8 as LBC

import System.Directory   (removeFile)
import System.Environment (lookupEnv)

import Test.Tasty         (testGroup, TestTree, TestName)
import Test.Tasty.Golden  (goldenVsString, goldenVsFile)
import Test.Tasty.HUnit   (assert, Assertion, testCase)

import Test.Tasty.Runners hiding (Result)
import System.Random (randomRIO)

import Data.SBV

import Data.Maybe(fromMaybe, catMaybes)

import System.FilePath ((</>), (<.>))

import Data.SBV.Internals (runSymbolic, Symbolic, Result, SBVRunMode(..), IStage(..))

---------------------------------------------------------------------------------------
-- Test environment
data TravisOS = TravisLinux
              | TravisOSX
              | TravisWindows    -- Travis actually doesn't support windows yet. This is "reserved" for future
              deriving Show

data TestEnvironment = TestEnvLocal
                     | TestEnvTravis TravisOS
                     | TestEnvUnknown
                     deriving Show

getTestEnvironment :: IO TestEnvironment
getTestEnvironment = do mbTestEnv <- lookupEnv "SBV_TEST_ENVIRONMENT"

                        case mbTestEnv of
                          Just "local" -> return   TestEnvLocal
                          Just "linux" -> return $ TestEnvTravis TravisLinux
                          Just "osx"   -> return $ TestEnvTravis TravisOSX
                          Just "win"   -> return $ TestEnvTravis TravisWindows
                          Just other   -> do putStrLn $ "Ignoring unexpected test env value: " ++ show other
                                             return TestEnvUnknown
                          Nothing      -> return TestEnvUnknown

-- | Checks that a particular result shows as @s@
showsAs :: Show a => a -> String -> Assertion
showsAs r s = assert $ show r == s

goldFile :: FilePath -> FilePath
goldFile nm = "SBVTestSuite" </> "GoldFiles" </> nm <.> "gold"

goldenString :: TestName -> IO String -> TestTree
goldenString n res = goldenVsString n (goldFile n) (fmap LBC.pack res)

goldenVsStringShow :: Show a => TestName -> IO a -> TestTree
goldenVsStringShow n res = goldenVsString n (goldFile n) (fmap (LBC.pack . show) res)

goldenCapturedIO :: TestName -> (FilePath -> IO ()) -> TestTree
goldenCapturedIO n res = goldenVsFile n gf gfTmp (rm gfTmp >> res gfTmp)
  where gf    = goldFile n
        gfTmp = gf ++ "_temp"

        rm f = removeFile f `C.catch` (\(_ :: C.SomeException) -> return ())

-- | Count the number of models
numberOfModels :: Provable a => a -> IO Int
numberOfModels p = do AllSatResult (_, _, rs) <- allSat p
                      return $ length rs

-- | Symbolicly run a SAT instance using the default config
runSAT :: Symbolic a -> IO Result
runSAT cmp = snd <$> runSymbolic (SMTMode ISetup True defaultSMTCfg) cmp

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

-- | Picking a certain percent of tests.
pickTests :: Int -> TestTree -> IO TestTree
pickTests d origTests = fromMaybe noTestsSelected <$> walk origTests
   where noTestsSelected = TestGroup "pickTests.NoTestsSelected" []

         walk PlusTestOptions{} = error "pickTests: Unexpected PlusTestOptions"
         walk WithResource{}    = error "pickTests: Unexpected WithResource"
         walk AskOptions{}      = error "pickTests: Unexpected AskOptions"
         walk t@SingleTest{}    = do c <- randomRIO (0, 99)
                                     if c < d
                                        then return $ Just t
                                        else return Nothing
         walk (TestGroup tn ts) = do cs <- catMaybes <$> mapM walk ts
                                     case cs of
                                       [] -> return Nothing
                                       _  -> return $ Just $ TestGroup tn cs
