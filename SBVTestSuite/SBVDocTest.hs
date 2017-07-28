module Main (main) where

import System.FilePath.Glob (glob)
import Test.DocTest (doctest)

import System.Exit (exitSuccess)

import Utils.SBVTestFramework (getTestEnvironment, TestEnvironment(..))

main :: IO ()
main = do testEnv <- getTestEnvironment

          putStrLn $ "SBVDocTest: Test platform: " ++ show testEnv

          case testEnv of
            TestEnvLocal     -> runDocTest
            TestEnvTravis _  -> runDocTest
            TestEnvUnknown   -> do putStrLn "Unknown test environment, skipping doctests"
                                   exitSuccess
 where runDocTest = glob "Data/SBV/**/*.hs" >>= doctest
