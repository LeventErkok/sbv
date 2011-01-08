{- (c) Copyright Levent Erkok. All rights reserved.
--
-- The sbv library is distributed with the BSD3 license. See the LICENSE file
-- in the distribution for details.
-}

module Main(main, createGolds) where

import Control.Monad(when)
import Test.HUnit
import System.Directory(doesDirectoryExist, findExecutable)
import System.Environment(getArgs)
import System.Exit
import System.FilePath ((</>))

import Data.SBV
import Data.SBV.Utils.SBVTest
import Paths_sbv(getDataDir)

-- To add a new collection of tests, import below and add to testCollection variable
import qualified Data.SBV.Examples.Arrays.Memory                 as T01 (testSuite)
import qualified Data.SBV.Examples.Basics.BasicTests             as T02 (testSuite)
import qualified Data.SBV.Examples.Basics.Higher                 as T03 (testSuite)
import qualified Data.SBV.Examples.Basics.Index                  as T04 (testSuite)
import qualified Data.SBV.Examples.Basics.ProofTests             as T05 (testSuite)
import qualified Data.SBV.Examples.Basics.QRem                   as T06 (testSuite)
import qualified Data.SBV.Examples.Basics.UnsafeFunctionEquality as T07 (testSuite)
import qualified Data.SBV.Examples.BitPrecise.BitTricks          as T08 (testSuite)
import qualified Data.SBV.Examples.BitPrecise.Legato             as T09 (testSuite)
import qualified Data.SBV.Examples.CRC.CCITT                     as T10 (testSuite)
import qualified Data.SBV.Examples.CRC.CCITT_Unidir              as T11 (testSuite)
import qualified Data.SBV.Examples.CRC.GenPoly                   as T12 (testSuite)
import qualified Data.SBV.Examples.CRC.Parity                    as T13 (testSuite)
import qualified Data.SBV.Examples.CRC.USB5                      as T14 (testSuite)
import qualified Data.SBV.Examples.Puzzles.DogCatMouse           as T15 (testSuite)

testCollection :: [SBVTestSuite]
testCollection = [
       T01.testSuite
     , T02.testSuite
     , T03.testSuite
     , T04.testSuite
     , T05.testSuite
     , T06.testSuite
     , T07.testSuite
     , T08.testSuite
     , T09.testSuite
     , T10.testSuite
     , T11.testSuite
     , T12.testSuite
     , T13.testSuite
     , T14.testSuite
     , T15.testSuite
     ]
-- No user serviceable parts below..

main :: IO ()
main = getArgs >>= run False

createGolds :: IO ()
createGolds = run True ["SBVUnitTest/GoldFiles"]

checkGoldDir :: FilePath -> IO ()
checkGoldDir gd = do e <- doesDirectoryExist gd
                     when (not e) $
                             do putStrLn $ "*** Cannot locate gold file repository!"
                                putStrLn $ "*** Please call with one argument, the directory name of the gold files."
                                putStrLn $ "*** Cannot run test cases, exiting."
                                exitWith $ ExitFailure 1

checkDefaultSolver :: IO ()
checkDefaultSolver = do mbP <- findExecutable ex
                        case mbP of
                          Nothing -> do putStrLn $ "*** Cannot find default SMT solver executable for " ++ nm
                                        putStrLn $ "*** Please make sure the executable " ++ show ex
                                        putStrLn $ "*** is installed and is in your path."
                                        putStrLn $ "*** Cannot run test cases, exiting."
                                        exitWith $ ExitFailure 1
                          Just p  -> putStrLn $ "*** Using solver : " ++ nm ++ " (" ++ show p ++ ")"
 where ex = executable $ solver $ defaultSMTCfg
       nm = name $ solver $ defaultSMTCfg

run :: Bool -> [String] -> IO ()
run shouldCreate [gd] =
        do putStrLn $ "*** Starting SBV unit tests..\n*** Gold files at: " ++ show gd
           checkGoldDir gd
           checkDefaultSolver
           let mkTst (SBVTestSuite f) = f $ generateGoldCheck gd shouldCreate
           cts <- runTestTT $ TestList $ map mkTst testCollection
           decide cts
run shouldCreate [] = getDataDir >>= \d -> run shouldCreate[d </> "SBVUnitTest" </> "GoldFiles"]
run _            _  = error "SBVUnitTests.run: impossible happened!"

decide :: Counts -> IO ()
decide cts@(Counts c t e f) = do
        when (c /= t) $ putStrLn $ "*** Not all test cases were tried. (Only tested " ++ show t ++ " of " ++ show c ++ ")"
        when (e /= 0) $ putStrLn $ "*** " ++ show e ++ " (of " ++ show c ++ ") test cases in error."
        when (f /= 0) $ putStrLn $ "*** " ++ show f ++ " (of " ++ show c ++ ") test cases failed."
        if (c == t && e == 0 && f == 0)
           then do putStrLn $ "All " ++ show c ++ " test cases successfully passed."
                   exitWith $ ExitSuccess
           else exitWith $ ExitFailure 2
