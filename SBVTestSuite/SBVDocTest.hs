module Main (main) where

import System.FilePath.Glob (glob)
import Test.DocTest (doctest)

import Utils.SBVTestFramework (getTestEnvironment, TestEnvironment(..))

main :: IO ()
main = do testEnv <- getTestEnvironment

          putStrLn $ "SBVDocTest: Test platform: " ++ show testEnv

          case testEnv of
            Local         -> runDocTest
            RemoteLinux   -> runDocTest
            RemoteOSX     -> return () -- TODO: What's the right test-suite here?
            RemoteWindows -> return () -- TODO: What's the right test-suite here?
            RemoteUnknown -> return ()
 where runDocTest = glob "Data/SBV/**/*.hs" >>= doctest
