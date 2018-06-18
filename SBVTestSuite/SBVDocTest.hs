module Main (main) where

import System.FilePath.Glob (glob)
import Test.DocTest (doctest)

import Data.Char (toLower)
import Data.List (isSuffixOf)

import System.Exit (exitSuccess)

import Utils.SBVTestFramework (getTestEnvironment, TestEnvironment(..), CIOS(..))

import System.Random (randomRIO)

main :: IO ()
main = do (testEnv, testPercentage) <- getTestEnvironment

          putStrLn $ "SBVDocTest: Test platform: " ++ show testEnv

          case testEnv of
            TestEnvLocal   -> runDocTest False False 100
            TestEnvCI env  -> if testPercentage < 50
                              then do putStrLn $ "Test percentage below tresheold, skipping doctest: " ++ show testPercentage
                                      exitSuccess
                              else runDocTest (env == CIWindows) True testPercentage
            TestEnvUnknown  -> do putStrLn "Unknown test environment, skipping doctests"
                                  exitSuccess

 where runDocTest onWindows onRemote tp = do srcFiles <- glob "Data/SBV/**/*.hs"
                                             docFiles <- glob "Documentation/SBV/**/*.hs"

                                             let allFiles  = srcFiles ++ docFiles
                                                 testFiles = filter (\nm -> not (skipWindows nm || skipRemote nm)) allFiles

                                                 args = ["--fast", "--no-magic"]

                                             tfs <- pickPercentage tp testFiles

                                             doctest $ args ++ tfs

         where noGood nm sl =  any (`isSuffixOf` map toLower nm) $ map (map toLower) sl

               skipWindows nm
                 | not onWindows = False
                 | True          = noGood nm skipList
                 where skipList = [ "NoDiv0.hs"         -- Has a safety check and windows paths are printed differently
                                  , "BrokenSearch.hs"   -- Ditto
                                  ]
               skipRemote nm
                 | not onRemote = False
                 | True         = noGood nm skipList
                 where skipList = [ "Interpolants.hs"  -- The following test requires mathSAT, so can't run on remote
                                  , "HexPuzzle.hs"     -- Doctest is way too slow on this with ghci loading, sigh
                                  , "MultMask.hs"      -- Also, quite slow
                                  ]

-- Pick (about) the given percentage of files
pickPercentage :: Int -> [String] -> IO [String]
pickPercentage 100 xs = return xs
pickPercentage   0 _  = return []
pickPercentage   p xs = concat <$> mapM pick xs
  where pick f = do c <- randomRIO (0, 100)
                    return [f | c >= p]
