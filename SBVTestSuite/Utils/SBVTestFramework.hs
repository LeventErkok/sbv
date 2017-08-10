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
        , CIOS(..), TestEnvironment(..), getTestEnvironment
        , pickTests
        -- module exports to simplify life
        , module Test.Tasty
        , module Test.Tasty.HUnit
        , module Data.SBV
        ) where

import qualified Control.Exception as C

import qualified Data.ByteString.Lazy.Char8 as LBC
import qualified Data.ByteString as BS

import System.Directory   (removeFile)
import System.Environment (lookupEnv)

import Test.Tasty         (testGroup, TestTree, TestName)
import Test.Tasty.HUnit   (assert, Assertion, testCase)

import Test.Tasty.Golden           (goldenVsString)
import Test.Tasty.Golden.Advanced  (goldenTest)

import Test.Tasty.Runners hiding (Result)
import System.Random (randomRIO)

import Data.SBV

import Data.Char (chr, ord, isDigit)

import Data.Maybe(fromMaybe, catMaybes)

import System.FilePath ((</>), (<.>))

import Data.SBV.Internals (runSymbolic, Symbolic, Result, SBVRunMode(..), IStage(..))

---------------------------------------------------------------------------------------
-- Test environment; continuous integration
data CIOS = CILinux
          | CIOSX
          | CIWindows
          deriving Show

data TestEnvironment = TestEnvLocal
                     | TestEnvCI CIOS
                     | TestEnvUnknown
                     deriving Show

getTestEnvironment :: IO (TestEnvironment, Int)
getTestEnvironment = do mbTestEnv  <- lookupEnv "SBV_TEST_ENVIRONMENT"
                        mbTestPerc <- lookupEnv "SBV_HEAVYTEST_PERCENTAGE"

                        env <- case mbTestEnv of
                                 Just "local" -> return   TestEnvLocal
                                 Just "linux" -> return $ TestEnvCI CILinux
                                 Just "osx"   -> return $ TestEnvCI CIOSX
                                 Just "win"   -> return $ TestEnvCI CIWindows
                                 Just other   -> do putStrLn $ "Ignoring unexpected test env value: " ++ show other
                                                    return TestEnvUnknown
                                 Nothing      -> return TestEnvUnknown

                        perc <- case mbTestPerc of
                                 Just n | all isDigit n -> return (read n)
                                 Just n                 -> do putStrLn $ "Ignoring unexpected test percentage value: " ++ show n
                                                              return 100
                                 Nothing                -> return 100

                        return (env, perc)

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
goldenCapturedIO n res = doTheDiff n gf gfTmp (rm gfTmp >> res gfTmp)
  where gf    = goldFile n
        gfTmp = gf ++ "_temp"

        rm f = removeFile f `C.catch` (\(_ :: C.SomeException) -> return ())

-- | When comparing ignore \r's for windows's sake
doTheDiff :: TestName -> FilePath -> FilePath -> IO () -> TestTree
doTheDiff nm ref new act = goldenTest nm (BS.readFile ref) (act >> BS.readFile new) cmp upd
   where upd = BS.writeFile ref

         cmp :: BS.ByteString -> BS.ByteString -> IO (Maybe String)
         cmp x y
          | cleanUp x == cleanUp y = return Nothing
          | True                   = return $ Just $ unlines $ [ "Discrepancy found. Expected: " ++ ref
                                                                 , "============================================"
                                                                 ]
                                                              ++ lines xs
                                                              ++ [ "Got: " ++ new
                                                                 , "============================================"
                                                                 ]
                                                              ++ lines ys
          where xs = map (chr . fromIntegral) $ BS.unpack x
                ys = map (chr . fromIntegral) $ BS.unpack y

         -- deal with insane Windows \r stuff
         cleanUp = BS.filter (/= slashr)
         slashr  = fromIntegral (ord '\r')

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
