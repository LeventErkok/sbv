module Main (main) where

import System.FilePath.Glob (glob)
import Test.DocTest (doctest)

import Data.Char (toLower)
import Data.List (isSuffixOf)

import System.Exit (exitSuccess)

import Utils.SBVTestFramework (getTestEnvironment, TestEnvironment(..), CIOS(..))

main :: IO ()
main = do (testEnv, _) <- getTestEnvironment

          putStrLn $ "SBVDocTest: Test platform: " ++ show testEnv

          case testEnv of
            TestEnvLocal        -> runDocTest False
            TestEnvCI CIWindows -> runDocTest True
            TestEnvCI _         -> runDocTest False
            TestEnvUnknown      -> do putStrLn "Unknown test environment, skipping doctests"
                                      exitSuccess
 where runDocTest windowsSkip = do allFiles <- glob "Data/SBV/**/*.hs"
                                   let testFiles
                                         | windowsSkip = filter (not . bad) allFiles
                                         | True        = allFiles
                                   doctest testFiles

       -- The following test has a path encoded in its output, and hence fails on Windows
       -- since it has the c:\blah\blah format. Skip it:
       bad fn = "nodiv0.hs" `isSuffixOf` map toLower fn

