module Main (main) where

import System.FilePath.Glob (glob)
import Test.DocTest (doctest)

import Data.Char (toLower)
import Data.List (isSuffixOf)

import System.Exit (exitSuccess)

import Utils.SBVTestFramework (getTestEnvironment, TestEnvironment(..), CIOS(..))

main :: IO ()
main = do (testEnv, testPercentage) <- getTestEnvironment

          putStrLn $ "SBVDocTest: Test platform: " ++ show testEnv

          case testEnv of
            TestEnvLocal   -> runDocTest False False
            TestEnvCI env  -> if testPercentage < 50
                              then do putStrLn $ "Test percentage below tresheold, skipping doctest: " ++ show testPercentage
                                      exitSuccess
                              else runDocTest (env == CIWindows) True
            TestEnvUnknown  -> do putStrLn "Unknown test environment, skipping doctests"
                                  exitSuccess

 where runDocTest onWindows onRemote = do srcFiles <- glob "Data/SBV/**/*.hs"
                                          docFiles <- glob "Documentation/SBV/**/*.hs"

                                          let allFiles  = srcFiles ++ docFiles
                                              testFiles = filter (\nm -> not (skipWindows nm || skipRemote nm)) allFiles

                                              args = ["--fast", "--no-magic"]

                                          doctest $ args ++ testFiles

         where skipWindows nm
                 | not onWindows = False
                 | True          = -- The following test has a path encoded in its output, and hence fails on Windows
                                   -- since it has the c:\blah\blah format. Skip it:
                                   "nodiv0.hs" `isSuffixOf` map toLower nm

               skipRemote nm
                 | not onRemote = False
                 | True         = -- The following test requires mathSAT, so can't run on remote
                                  "interpolants.hs" `isSuffixOf` map toLower nm
