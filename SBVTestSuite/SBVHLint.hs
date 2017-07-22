module Main (main) where

import Utils.SBVTestFramework (getTestEnvironment, TestEnvironment(..))

import Language.Haskell.HLint (hlint)
import System.Exit (exitFailure, exitSuccess)

arguments :: [String]
arguments =
    [ "Data"
    , "SBVTestSuite"
    , "-i", "Use otherwise"
    ]

main :: IO ()
main = do
    testEnv <- getTestEnvironment

    putStrLn $ "SBVHLint: Test platform: " ++ show testEnv

    case testEnv of
      Local         -> runHLint
      RemoteLinux   -> runHLint
      RemoteOSX     -> exitSuccess -- TODO: What's the right test-suite here?
      RemoteWindows -> exitSuccess -- TODO: What's the right test-suite here?
      RemoteUnknown -> exitSuccess
 where runHLint = do hints <- hlint arguments
                     if null hints
                        then exitSuccess
                        else exitFailure
